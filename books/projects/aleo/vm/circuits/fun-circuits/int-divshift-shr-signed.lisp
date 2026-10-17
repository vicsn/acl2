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

(include-book "int-divshift-sshr-bits")

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defun int-divshift-ss-expt-ind (k)
   (if (zp k) t (int-divshift-ss-expt-ind (1- k)))))

(defruledl int-divshift-ss-below-expt-plus
  (implies (and (natp cur)
                (natp a)
                (natp k)
                (< cur (expt 2 a)))
           (< cur (expt 2 (+ a k))))
  :hints (("Goal"
           :induct (int-divshift-ss-expt-ind k)
           :in-theory (enable expt))))

(defruledl int-divshift-ss-double-power
  (implies (natp i)
           (equal (+ (expt 2 i) (expt 2 i))
                  (expt 2 (+ 1 i))))
  :enable acl2::expt-of-+-of-1-arg2)

(defruledl int-divshift-ss-below-wider-power
  (implies (and (natp cur)
                (natp width)
                (natp i)
                (< cur (expt 2 (+ width (expt 2 i)))))
           (< cur (expt 2 (+ width (expt 2 (+ 1 i))))))
  :do-not-induct t
  :use (:instance int-divshift-ss-below-expt-plus
                  (a (+ width (expt 2 i)))
                  (k (expt 2 i)))
  :enable int-divshift-ss-double-power
  :disable (int-divshift-ss-below-expt-plus expt acl2::expt-of-+-of-1-arg2))

(defruledl int-divshift-ss-after-bound
  (implies (and (natp width)
                (natp cur)
                (natp i)
                (bitp bit)
                (< cur (expt 2 (+ width (expt 2 i)))))
           (< (int-shift-after cur bit i)
              (expt 2 (+ width (expt 2 (+ 1 i))))))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal bit 1))
           :in-theory (e/d (int-shift-after
                            int-shift-pow
                            bitp
                            int-divshift-ss-below-wider-power)
                           (acl2::*-of-expt-and-expt-same-base)))
          ("Subgoal 1"
           :use (:instance acl2::<-of-*-and-*-cancel
                           (x1 cur)
                           (x2 (expt 2 (+ width (expt 2 i))))
                           (y (expt 2 (expt 2 i))))
           :in-theory (e/d (int-shift-after
                            int-shift-pow
                            acl2::*-of-expt-and-expt-same-base
                            int-divshift-ss-double-power)
                           (acl2::<-of-*-and-*-cancel)))))

(defruledl int-divshift-ss-cur-below-step
  (implies (and (natp cur)
                (natp n)
                (natp i)
                (< cur (expt 2 n)))
           (< cur (expt 2 (+ n (expt 2 i)))))
  :do-not-induct t
  :use (:instance int-divshift-ss-below-expt-plus
                  (a n)
                  (k (expt 2 i)))
  :disable (int-divshift-ss-below-expt-plus expt))

(defruledl int-divshift-sshr-after-below-prime
  (implies (and (equal p (base-prime))
                (integer-widthp n)
                (not (equal n 128))
                (natp c)
                (natp i)
                (bitp b)
                (< i (1- (integer-length n)))
                (< c (expt 2 (+ n (expt 2 i)))))
           (< (int-shift-after c b i) p))
  :do-not-induct t
  :use ((:instance int-shift-cur-times-pow-below-prime (cur c))
        (:instance le-times (a c) (k (int-shift-pow i)))
        (:instance pow-pos))
  :in-theory (e/d (int-shift-after bitp)
                  (int-shift-cur-times-pow-below-prime int-shift-pow
                   base-prime (:e base-prime)))
  :prep-lemmas
  ((defruled le-times
     (implies (and (natp a) (posp k)) (<= a (* a k)))
     :hints (("Goal" :nonlinearp t)))
   (defruled pow-pos
     (posp (int-shift-pow i))
     :enable int-shift-pow)))

(defruledl int-divshift-ss-atom-when-len-0
  (implies (equal (len x) 0)
           (not (consp x))))

(defruled int-divshift-sshr-var-chain-sound
  :short "The masked tail selects force the plain shift witnesses of
          @('cur + msb'), each minus the msb."
  (implies (and (symbolp prev)
                (symbolp m)
                (symbol-listp ebits)
                (symbol-listp nexts)
                (equal (len nexts) (len ebits))
                (natp i)
                (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg prev)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg ebits)
                (r1cs::valuation-binds-allp asg nexts)
                (natp (lookup-equal prev asg))
                (bitp (lookup-equal m asg))
                (bit-listp (lookup-equal-list ebits asg))
                (<= (+ i (len ebits)) (1- (integer-length n)))
                (< (+ (lookup-equal prev asg) (lookup-equal m asg))
                   (expt 2 (+ n (expt 2 i))))
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-sshr-var-chain prev ebits nexts m i p)
                 asg p))
           (equal (lookup-equal-list nexts asg)
                  (int-divshift-sub-each
                   (int-shift-witness-values
                    (+ (lookup-equal prev asg) (lookup-equal m asg))
                    (lookup-equal-list ebits asg)
                    i)
                   (lookup-equal m asg))))
  :hints (("Goal"
           :induct (int-divshift-sshr-var-chain prev ebits nexts m i p)
           :in-theory (e/d (int-divshift-sshr-var-chain
                            int-divshift-ss-atom-when-len-0
                            int-shift-witness-values
                            int-divshift-sub-each
                            lookup-equal-list
                            car-of-lookup-equal-list
                            lookup-equal-list-of-cdr
                            r1cs::r1cs-constraints-holdp-of-append
                            r1cs::valuation-binds-allp
                            bit-listp
                            symbol-listp)
                           (mod
                            floor
                            lookup-equal
                            int-shift-after
                            int-shift-pow
                            pfield::add
                            pfield::mul
                            pfield::neg)))
          ("Subgoal *1/2"
           :use ((:instance int-divshift-ss-after-bound
                            (width n)
                            (cur (+ (lookup-equal prev asg)
                                    (lookup-equal m asg)))
                            (bit (lookup-equal (car ebits) asg))
                            (i i))
                 (:instance int-divshift-sshr-after-below-prime
                            (c (+ (lookup-equal prev asg)
                                  (lookup-equal m asg)))
                            (b (lookup-equal (car ebits) asg)))
                 (:instance int-divshift-sshr-after-mono
                            (c (+ (lookup-equal prev asg)
                                  (lookup-equal m asg)))
                            (b (lookup-equal (car ebits) asg)))
                 (:instance int-divshift-sshr-var-step-iff
                            (bit (car ebits))
                            (cur prev)
                            (next (car nexts))
                            (i i))))))

(defruledl int-divshift-ss-dot-be-vector
  (implies (and (symbol-listp xs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (bit-listp (lookup-equal-list xs asg)))
           (equal (r1cs::dot-product (int-be-pow2sum-vector xs w) asg p)
                  (mod (int-be-weighted (lookup-equal-list xs asg) w) p)))
  :induct (int-be-pow2sum-vector xs w)
  :enable (int-be-pow2sum-vector
           int-be-weighted
           r1cs::dot-product
           lookup-equal-list
           r1cs::valuation-binds-allp
           pfield::add
           pfield::mul
           bit-listp))

(defruledl int-divshift-ss-be-weighted-rev
  (implies (bit-listp vals)
           (equal (int-be-weighted vals (1- (len vals)))
                  (lebits=>nat (rev vals))))
  :induct (len vals)
  :enable (int-be-weighted
           rev
           acl2::lebits=>nat-of-append
           acl2::lebits=>nat-of-cons
           bit-listp))
(defruledl int-divshift-ss-dot-of-cons-single
  (implies (and (syntaxp (not (equal rest ''nil)))
                (posp p))
           (equal (r1cs::dot-product (cons (list 1 v) rest) asg p)
                  (pfield::add (r1cs::dot-product (list (list 1 v)) asg p)
                               (r1cs::dot-product rest asg p)
                               p)))
  :use (:instance r1cs::dot-product-of-append
                  (r1cs::vec1 (list (list 1 v))) (r1cs::vec2 rest)
                  (r1cs::valuation asg) (r1cs::prime p))
  :disable r1cs::dot-product-of-append)

(defruledl int-divshift-ss-len-pos-when-consp
  (implies (consp x) (< 0 (len x))))

(defruledl int-divshift-sshr-first-step-iff
  (implies (and (symbolp bit)
                (symbol-listp xs)
                (consp xs)
                (symbolp next)
                (symbolp m)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg bit)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-bindsp asg next)
                (r1cs::valuation-bindsp asg m)
                (bitp (lookup-equal bit asg))
                (bitp (lookup-equal m asg))
                (bit-listp (lookup-equal-list xs asg))
                (< (int-shift-after (+ (lebits=>nat
                                        (rev (lookup-equal-list xs asg)))
                                       (lookup-equal m asg))
                                    (lookup-equal bit asg) 0)
                   p))
           (equal (r1cs::r1cs-constraints-holdp
                   (int-divshift-sshr-first-step bit xs next m p) asg p)
                  (equal (lookup-equal next asg)
                         (- (int-shift-after
                             (+ (lebits=>nat (rev (lookup-equal-list xs asg)))
                                (lookup-equal m asg))
                             (lookup-equal bit asg) 0)
                            (lookup-equal m asg)))))
  :do-not-induct t
  :use ((:instance int-divshift-ss-dot-be-vector (w (nfix (1- (len xs)))))
        (:instance int-divshift-ss-be-weighted-rev
                   (vals (lookup-equal-list xs asg)))
        (:instance int-divshift-sshr-after-mono
                   (c (+ (lebits=>nat (rev (lookup-equal-list xs asg)))
                         (lookup-equal m asg)))
                   (b (lookup-equal bit asg))
                   (i 0))
        (:instance int-divshift-sshr-core
                   (c (lebits=>nat (rev (lookup-equal-list xs asg))))
                   (b (lookup-equal bit asg))
                   (mv (lookup-equal m asg))
                   (next (lookup-equal next asg))
                   (i 0)))
  :in-theory (e/d (int-divshift-sshr-first-step
                   r1cs::r1cs-constraints-holdp
                   r1cs::r1cs-constraint-holdsp
                   r1cs::dot-product-of-append
                   dot-product-of-vector-neg-prime-to-neg-of-dot-product
                   len-of-lookup-equal-list nfix
                   int-divshift-ss-len-pos-when-consp
                   int-divshift-ss-dot-of-cons-single
                   r1cs::dot-product
                   pfield::mul pfield::add pfield::neg pfield::sub
                   acl2::mod-when-< bitp)
                  (mod floor lookup-equal int-divshift-sshr-core
                   int-divshift-ss-dot-be-vector int-divshift-ss-be-weighted-rev
                   int-divshift-sshr-after-mono
                   int-be-pow2sum-vector
                   int-shift-after int-shift-scale)))

(defruled int-divshift-sshr-chain-sound
  :short "The masked selects force the plain shift witnesses of
          @('R + msb'), each minus the msb."
  (implies (and (symbol-listp xs)
                (symbol-listp ebits)
                (symbol-listp nexts)
                (symbolp m)
                (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (equal (len xs) n)
                (equal (len ebits) (1- (integer-length n)))
                (equal (len nexts) (len ebits))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ebits)
                (r1cs::valuation-binds-allp asg nexts)
                (r1cs::valuation-bindsp asg m)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ebits asg))
                (bitp (lookup-equal m asg))
                (< (+ (lebits=>nat (rev (lookup-equal-list xs asg)))
                      (lookup-equal m asg))
                   (expt 2 (+ n 1)))
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-sshr-first-step (car ebits) xs (car nexts) m p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-sshr-var-chain (car nexts) (cdr ebits)
                                              (cdr nexts) m 1 p)
                 asg p))
           (equal (lookup-equal-list nexts asg)
                  (int-divshift-sub-each
                   (int-shift-witness-values
                    (+ (lebits=>nat (rev (lookup-equal-list xs asg)))
                       (lookup-equal m asg))
                    (lookup-equal-list ebits asg)
                    0)
                   (lookup-equal m asg))))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64))
           :use ((:instance int-divshift-sshr-first-step-iff
                            (bit (car ebits))
                            (next (car nexts)))
                 (:instance int-divshift-sshr-after-below-prime
                            (c (+ (lebits=>nat
                                   (rev (lookup-equal-list xs asg)))
                                  (lookup-equal m asg)))
                            (b (lookup-equal (car ebits) asg))
                            (i 0))
                 (:instance int-divshift-sshr-after-mono
                            (c (+ (lebits=>nat
                                   (rev (lookup-equal-list xs asg)))
                                  (lookup-equal m asg)))
                            (b (lookup-equal (car ebits) asg))
                            (i 0))
                 (:instance int-divshift-ss-after-bound
                            (width n)
                            (cur (+ (lebits=>nat
                                     (rev (lookup-equal-list xs asg)))
                                    (lookup-equal m asg)))
                            (bit (lookup-equal (car ebits) asg))
                            (i 0))
                 (:instance int-divshift-sshr-var-chain-sound
                            (prev (car nexts))
                            (ebits (cdr ebits))
                            (nexts (cdr nexts))
                            (i 1)))
           :in-theory (e/d (int-shift-witness-values
                            int-divshift-sub-each
                            lookup-equal-list
                            car-of-lookup-equal-list
                            lookup-equal-list-of-cdr
                            r1cs::valuation-binds-allp
                            bit-listp
                            symbol-listp
                            integer-widthp)
                           (int-divshift-sshr-first-step-iff
                            int-divshift-sshr-after-below-prime
                            int-divshift-sshr-after-mono
                            int-divshift-ss-after-bound
                            int-divshift-sshr-var-chain-sound
                            int-divshift-sshr-first-step
                            int-divshift-sshr-var-chain
                            mod floor lookup-equal
                            int-shift-after int-shift-pow
                            pfield::add pfield::mul)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled int-divshift-sshr-last-sub-each
  (implies (consp vals)
           (equal (car (last (int-divshift-sub-each vals m)))
                  (- (car (last vals)) m)))
  :induct (len vals)
  :enable (int-divshift-sub-each last))

(defruled int-divshift-sshr-msb-wire
  (implies (and (symbol-listp xs)
                (consp xs)
                (r1cs::valuation-binds-allp asg xs))
           (and (symbolp (car (last xs)))
                (r1cs::valuation-bindsp asg (car (last xs)))
                (equal (lookup-equal (car (last xs)) asg)
                       (car (last (lookup-equal-list xs asg))))))
  :induct (len xs)
  :enable (last lookup-equal-list r1cs::valuation-binds-allp symbol-listp))

(defruled int-divshift-sshr-final-bound
  (implies (and (integer-widthp n)
                (natp r)
                (< r (expt 2 n))
                (bitp mv)
                (natp s)
                (< s n))
           (and (<= mv (* (+ r mv) (expt 2 s)))
                (< (* (+ r mv) (expt 2 s)) (expt 2 (* 2 n)))))
  :do-not-induct t
  :use ((:instance le-mul (a (+ r mv)) (b (expt 2 n)) (k (expt 2 s)))
        (:instance pos-le-mul (a (+ r mv)) (k (expt 2 s)))
        (:instance acl2::expt-of-+ (r 2) (i1 n) (i2 s))
        (:instance mono)
        (:instance expt-pos (k s))
        (:instance expt-pos (k n))
        (:instance posp-when-integer-widthp))
  :in-theory (union-theories '(bitp natp posp (:e fix))
                             (theory 'minimal-theory))
  :prep-lemmas
  ((defruled expt-pos
     (implies (natp k) (posp (expt 2 k))))
   (defruled mono
     (implies (and (natp n) (natp s) (< s n))
              (< (expt 2 (+ n s)) (expt 2 (* 2 n))))
     :use (:instance acl2::expt-monotone-strong (r 2) (i (+ n s)) (j (* 2 n)))
     :disable acl2::expt-monotone-strong)
   (defruled le-mul
     (implies (and (natp a) (natp b) (<= a b) (posp k))
              (<= (* a k) (* b k)))
     :hints (("Goal" :nonlinearp t)))
   (defruled pos-le-mul
     (implies (and (natp a) (posp k))
              (<= a (* a k)))
     :hints (("Goal" :nonlinearp t)))))

(defruled int-divshift-sshr-run-final
  (implies (and (integer-widthp n)
                (natp c)
                (natp e))
           (equal (int-shift-run c (int->lebits (mod e n)
                                                (1- (integer-length n)))
                                 0)
                  (* c (expt 2 (mod e n)))))
  :do-not-induct t
  :use ((:instance int-shift-run-value
                   (cur c)
                   (bits (int->lebits (mod e n) (1- (integer-length n))))
                   (i 0))
        (:instance lebits=>nat-of-int->lebits
                   (x (mod e n))
                   (n (1- (integer-length n)))))
  :in-theory (e/d (int-width-is-power-of-two
                   bit-listp-of-int->lebits-explicit
                   integer-widthp
                   posp-when-integer-widthp
                   acl2::mod-when-<
                   acl2::ifix-when-integerp)
                  (int-shift-run-value lebits=>nat-of-int->lebits
                   int->lebits mod)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro int-divshift-sshr-common-hyps ()
  '(and (equal p (base-prime))
        (primep p)
        (integer-widthp n)
        (not (equal n 128))
        (int-valuep x t n)
        (natp e)
        (symbol-listp xs)
        (symbol-listp ebits)
        (symbol-listp nexts)
        (symbol-listp zs)
        (equal (len xs) n)
        (equal (len ebits) (1- (integer-length n)))
        (equal (len nexts) (len ebits))
        (equal (len zs) (* 2 n))
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg ebits)
        (r1cs::valuation-binds-allp asg nexts)
        (r1cs::valuation-bindsp asg (car (last nexts)))
        (r1cs::valuation-binds-allp asg zs)
        (equal (lookup-equal-list xs asg) (int->lebits x n))
        (equal (lookup-equal-list ebits asg)
               (int->lebits (mod e n) (1- (integer-length n))))))

(defruled int-divshift-sshr-value-facts
  (implies (and (integer-widthp n) (int-valuep x t n))
           (and (bitp (car (last (int->lebits x n))))
                (natp (lebits=>nat (rev (int->lebits x n))))
                (< (lebits=>nat (rev (int->lebits x n))) (expt 2 n))
                (< (+ (lebits=>nat (rev (int->lebits x n)))
                      (car (last (int->lebits x n))))
                   (expt 2 (+ n 1)))
                (consp (int->lebits x n))
                (bit-listp (int->lebits x n))))
  :do-not-induct t
  :use ((:instance int-signed-msb)
        (:instance acl2::lebits=>nat-upper-bound
                   (digits (rev (int->lebits x n))))
        (:instance acl2::expt-of-+ (r 2) (i1 n) (i2 1)))
  :in-theory (e/d (bitp len-of-int->lebits bit-listp-of-int->lebits-explicit
                   posp-when-integer-widthp)
                  (int-signed-msb acl2::lebits=>nat-upper-bound
                   acl2::expt-of-+ int->lebits)))

(defruledl int-divshift-sshr-zs
  (implies (and (int-divshift-sshr-common-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-shr-signed-gadget xs ebits nexts zs p) asg p))
           (equal (lookup-equal-list zs asg)
                  (int->lebits
                   (+ (* (+ (lebits=>nat (rev (int->lebits x n)))
                            (car (last (int->lebits x n))))
                         (expt 2 (mod e n)))
                      (- (car (last (int->lebits x n)))))
                   (* 2 n))))
  :do-not-induct t
  :hints (("Goal"
           :cases ((equal n 8) (equal n 16) (equal n 32) (equal n 64))
           :use ((:instance int-divshift-sshr-value-facts)
                 (:instance int-divshift-sshr-msb-wire)
                 (:instance int-divshift-sshr-chain-sound
                            (m (car (last xs))))
                 (:instance int-shift-witness-last-is-run
                            (cur (+ (lebits=>nat (rev (int->lebits x n)))
                                    (car (last (int->lebits x n)))))
                            (bits (lookup-equal-list ebits asg))
                            (i 0))
                 (:instance int-divshift-sshr-run-final
                            (c (+ (lebits=>nat (rev (int->lebits x n)))
                                  (car (last (int->lebits x n))))))
                 (:instance int-divshift-sshr-last-sub-each
                            (vals (int-shift-witness-values
                                   (+ (lebits=>nat (rev (int->lebits x n)))
                                      (car (last (int->lebits x n))))
                                   (lookup-equal-list ebits asg)
                                   0))
                            (m (car (last (int->lebits x n)))))
                 (:instance car-of-lookup-equal-list
                            (keys (last nexts))
                            (alist asg))
                 (:instance last-of-lookup-equal-list
                            (keys nexts)
                            (alist asg))
                 (:instance int-divshift-sshr-final-bound
                            (r (lebits=>nat (rev (int->lebits x n))))
                            (mv (car (last (int->lebits x n))))
                            (s (mod e n)))
                 (:instance int-divshift-shift-lower-sound
                            (final (car (last nexts)))
                            (v (+ (* (+ (lebits=>nat (rev (int->lebits x n)))
                                        (car (last (int->lebits x n))))
                                     (expt 2 (mod e n)))
                                  (- (car (last (int->lebits x n))))))))
           :in-theory (e/d (int-divshift-shr-signed-gadget
                            r1cs::r1cs-constraints-holdp-of-append
                            bit-listp-of-int->lebits-explicit
                            len-of-int->lebits
                            consp-of-int-shift-witness-values
                            integer-widthp
                            posp-when-integer-widthp
                            acl2::mod-when-<
                            bitp)
                           (int-divshift-sshr-value-facts
                            int-divshift-sshr-msb-wire
                            int-divshift-sshr-chain-sound
                            int-shift-witness-last-is-run
                            int-divshift-sshr-run-final
                            int-divshift-sshr-last-sub-each
                            car-of-lookup-equal-list
                            last-of-lookup-equal-list
                            int-divshift-sshr-final-bound
                            int-divshift-shift-lower-sound
                            int-divshift-sshr-first-step
                            int-divshift-sshr-var-chain
                            int-shift-lower-gadget
                            int->lebits mod floor lookup-equal
                            int-shift-after int-shift-pow
                            pfield::add pfield::mul)))))

(defruledl int-divshift-sshr-spec
  (implies (and (integer-widthp n) (int-valuep x t n) (natp e))
           (and (equal (floor x (expt 2 (mod e n)))
                       (int-shr-wrapped-spec x e t n))
                (natp (mod e n))
                (< (mod e n) n)))
  :enable (int-shr-wrapped-spec int-valuep int-min int-max
           acl2::ifix-when-integerp posp-when-integer-widthp integer-widthp))

(defruled int-divshift-shr-wrapped-signed-gadget-sound
  :short "R1CS-SOUND of variable-mode signed @('shr_wrapped') for every
          width other than 128.  The result integer is the low @('n')
          bits of @('zs'), reversed: the value bits shifted down by
          @('e mod n') with the sign bit shifted in."
  (implies (and (int-divshift-sshr-common-hyps)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-shr-signed-gadget xs ebits nexts zs p) asg p))
           (and (equal (rev (take n (lookup-equal-list zs asg)))
                       (append (nthcdr (mod e n) (int->lebits x n))
                               (repeat (mod e n)
                                       (car (last (int->lebits x n))))))
                (equal (lebits->int (rev (take n (lookup-equal-list zs asg)))
                                    t)
                       (int-shr-wrapped-spec x e t n))))
  :do-not-induct t
  :use ((:instance int-divshift-sshr-zs)
        (:instance int-divshift-sshr-value-facts)
        (:instance int-divshift-sshr-spec)
        (:instance int-divshift-sshr-take-bits
                   (b (int->lebits x n))
                   (s (mod e n))
                   (mv (car (last (int->lebits x n)))))
        (:instance int-divshift-sshr-bits-signed (s (mod e n)))
        (:instance rev-take-l
                   (a (take n (lookup-equal-list zs asg)))
                   (u (nthcdr (mod e n) (int->lebits x n)))
                   (s (mod e n))
                   (v (car (last (int->lebits x n)))))
        (:instance len-of-int->lebits (x x) (n n))
        (:instance posp-when-integer-widthp (n n)))
  :in-theory (union-theories '(natp posp)
                             (theory 'minimal-theory))
  :prep-lemmas
  ((defruled rev-take-l
     (implies (equal a (rev (append u (repeat s v))))
              (equal (rev a) (append u (repeat s v)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(set-prover-step-limit 5000000)

(defruledl int-divshift-sshr-var-chain-complete
  (implies (and (symbolp prev)
                (symbolp m)
                (symbol-listp ebits)
                (symbol-listp nexts)
                (equal (len nexts) (len ebits))
                (natp i)
                (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg prev)
                (r1cs::valuation-bindsp asg m)
                (r1cs::valuation-binds-allp asg ebits)
                (r1cs::valuation-binds-allp asg nexts)
                (natp (lookup-equal prev asg))
                (bitp (lookup-equal m asg))
                (bit-listp (lookup-equal-list ebits asg))
                (<= (+ i (len ebits)) (1- (integer-length n)))
                (< (+ (lookup-equal prev asg) (lookup-equal m asg))
                   (expt 2 (+ n (expt 2 i))))
                (equal (lookup-equal-list nexts asg)
                       (int-divshift-sub-each
                        (int-shift-witness-values
                         (+ (lookup-equal prev asg) (lookup-equal m asg))
                         (lookup-equal-list ebits asg)
                         i)
                        (lookup-equal m asg))))
           (r1cs::r1cs-constraints-holdp
            (int-divshift-sshr-var-chain prev ebits nexts m i p)
            asg p))
  :hints (("Goal"
           :induct (int-divshift-sshr-var-chain prev ebits nexts m i p)
           :in-theory (e/d (int-divshift-sshr-var-chain
                            int-divshift-ss-atom-when-len-0
                            int-shift-witness-values
                            int-divshift-sub-each
                            lookup-equal-list
                            car-of-lookup-equal-list
                            lookup-equal-list-of-cdr
                            r1cs::r1cs-constraints-holdp-of-append
                            r1cs::valuation-binds-allp
                            bit-listp
                            symbol-listp)
                           (mod
                            floor
                            lookup-equal
                            int-shift-after
                            int-shift-pow
                            pfield::add
                            pfield::mul
                            pfield::neg)))
          ("Subgoal *1/2"
           :use ((:instance int-divshift-ss-after-bound
                            (width n)
                            (cur (+ (lookup-equal prev asg)
                                    (lookup-equal m asg)))
                            (bit (lookup-equal (car ebits) asg))
                            (i i))
                 (:instance int-divshift-sshr-after-below-prime
                            (c (+ (lookup-equal prev asg)
                                  (lookup-equal m asg)))
                            (b (lookup-equal (car ebits) asg)))
                 (:instance int-divshift-sshr-after-mono
                            (c (+ (lookup-equal prev asg)
                                  (lookup-equal m asg)))
                            (b (lookup-equal (car ebits) asg)))
                 (:instance int-divshift-sshr-var-step-iff
                            (bit (car ebits))
                            (cur prev)
                            (next (car nexts))
                            (i i))))))

(defruledl int-divshift-sshr-split-nexts
  (implies (and (consp bits)
                (consp nexts)
                (equal (lookup-equal-list nexts asg)
                       (int-divshift-sub-each
                        (int-shift-witness-values c bits i) m)))
           (and (equal (lookup-equal (car nexts) asg)
                       (- (int-shift-after c (car bits) i) m))
                (equal (lookup-equal-list (cdr nexts) asg)
                       (int-divshift-sub-each
                        (int-shift-witness-values
                         (int-shift-after c (car bits) i)
                         (cdr bits)
                         (+ 1 (nfix i)))
                        m))))
  :do-not-induct t
  :use ((:instance car-cdr-of-equal
                   (a (lookup-equal-list nexts asg))
                   (b (int-divshift-sub-each
                       (int-shift-witness-values c bits i) m))))
  :in-theory (e/d (int-shift-witness-values int-divshift-sub-each
                   lookup-equal-of-car lookup-equal-list-of-cdr)
                  (int-shift-after car-of-lookup-equal-list))
  :prep-lemmas
  ((defruled car-cdr-of-equal
     (implies (equal a b)
              (and (equal (car a) (car b)) (equal (cdr a) (cdr b)))))))

(defruled int-divshift-sshr-ilen
  (implies (integer-widthp n)
           (and (<= 4 (integer-length n))
                (natp n)))
  :enable integer-widthp)

(defruled int-divshift-sshr-chain-complete
  (implies (and (symbol-listp xs)
                (symbol-listp ebits)
                (symbol-listp nexts)
                (symbolp m)
                (equal p (base-prime))
                (primep p)
                (integer-widthp n)
                (not (equal n 128))
                (equal (len xs) n)
                (equal (len ebits) (1- (integer-length n)))
                (equal (len nexts) (len ebits))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ebits)
                (r1cs::valuation-binds-allp asg nexts)
                (r1cs::valuation-bindsp asg m)
                (bit-listp (lookup-equal-list xs asg))
                (bit-listp (lookup-equal-list ebits asg))
                (bitp (lookup-equal m asg))
                (< (+ (lebits=>nat (rev (lookup-equal-list xs asg)))
                      (lookup-equal m asg))
                   (expt 2 (+ n 1)))
                (equal (lookup-equal-list nexts asg)
                       (int-divshift-sub-each
                        (int-shift-witness-values
                         (+ (lebits=>nat (rev (lookup-equal-list xs asg)))
                            (lookup-equal m asg))
                         (lookup-equal-list ebits asg)
                         0)
                        (lookup-equal m asg))))
           (and (r1cs::r1cs-constraints-holdp
                 (int-divshift-sshr-first-step (car ebits) xs (car nexts) m p)
                 asg p)
                (r1cs::r1cs-constraints-holdp
                 (int-divshift-sshr-var-chain (car nexts) (cdr ebits)
                                              (cdr nexts) m 1 p)
                 asg p)))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance int-divshift-sshr-ilen)
                 (:instance int-divshift-sshr-split-nexts
                            (bits (lookup-equal-list ebits asg))
                            (c (+ (lebits=>nat
                                   (rev (lookup-equal-list xs asg)))
                                  (lookup-equal m asg)))
                            (i 0)
                            (m (lookup-equal m asg)))
                 (:instance int-divshift-sshr-first-step-iff
                            (bit (car ebits))
                            (next (car nexts)))
                 (:instance int-divshift-sshr-after-below-prime
                            (c (+ (lebits=>nat
                                   (rev (lookup-equal-list xs asg)))
                                  (lookup-equal m asg)))
                            (b (lookup-equal (car ebits) asg))
                            (i 0))
                 (:instance int-divshift-sshr-after-mono
                            (c (+ (lebits=>nat
                                   (rev (lookup-equal-list xs asg)))
                                  (lookup-equal m asg)))
                            (b (lookup-equal (car ebits) asg))
                            (i 0))
                 (:instance int-divshift-ss-after-bound
                            (width n)
                            (cur (+ (lebits=>nat
                                     (rev (lookup-equal-list xs asg)))
                                    (lookup-equal m asg)))
                            (bit (lookup-equal (car ebits) asg))
                            (i 0))
                 (:instance int-divshift-sshr-var-chain-complete
                            (prev (car nexts))
                            (ebits (cdr ebits))
                            (nexts (cdr nexts))
                            (i 1)))
           :in-theory (e/d (car-of-lookup-equal-list
                            lookup-equal-list-of-cdr
                            r1cs::valuation-binds-allp
                            bit-listp
                            symbol-listp
                            nfix)
                           (int-divshift-sshr-split-nexts
                            int-divshift-sshr-ilen
                            integer-widthp
                            int-divshift-sshr-first-step-iff
                            int-divshift-sshr-after-below-prime
                            int-divshift-sshr-after-mono
                            int-divshift-ss-after-bound
                            int-divshift-sshr-var-chain-complete
                            int-divshift-sshr-first-step
                            int-divshift-sshr-var-chain
                            int-shift-witness-values
                            int-divshift-sub-each
                            lookup-equal-list
                            mod floor lookup-equal
                            int-shift-after int-shift-pow
                            pfield::add pfield::mul)))))

