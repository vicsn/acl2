; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Concrete BHP, as snarkVM 7dc117d45 computes it (console/algorithms/src/bhp).
;
; BHPHasher<NUM_WINDOWS, WINDOW_SIZE> (hasher/mod.rs, hasher/hash_uncompressed.rs):
;   - setup derives one generator G_w per window w < NUM_WINDOWS by
;     Blake2Xs::hash_to_curve("Aleo.BHP.{NUM_WINDOWS}.{WINDOW_SIZE}.{domain}.{w}")
;     (cofactor cleared, so G_w is in the order-r subgroup or is zero), and
;     the window bases are 16^j G_w for j < WINDOW_SIZE;
;   - the lookup for a 3-bit chunk (b0, b1, b2) at position j of window w is
;     (1 + b0 + 2 b1) 16^j G_w, negated when b2 = 1; the combined lookup
;     (4 chunks at a time) is the sum of the four individual lookups;
;   - hash_uncompressed rejects inputs of at most 3 WINDOW_SIZE bits or more
;     than 3 WINDOW_SIZE NUM_WINDOWS bits, pads with zeros to a multiple of 3,
;     splits into windows of 3 WINDOW_SIZE bits and sums all lookups.
; Edwards addition is associative and commutative, so the sum is
; sum_w (s_w G_w) where s_w is hbhp-window-scalar of window w; we fold it
; left to right from zero, which is the order the circuit adds the windows.
;
; BHP<NUM_WINDOWS, WINDOW_SIZE> (mod.rs, hash_uncompressed.rs):
;   - the domain is the little-endian bits of the domain string bytes,
;     resized to 188 = 252 - 64 bits and reversed;
;   - hash_uncompressed splits the input into chunks of
;     3 WINDOW_SIZE NUM_WINDOWS - 252 bits; the first preimage is
;     domain ++ u64-le(len input) ++ chunk, each later one is the first 252
;     little-endian bits of the x-coordinate of the previous digest ++ chunk;
;     the digest starts at zero, so the empty input hashes to zero;
;   - hash is the x-coordinate of hash_uncompressed;
;   - commit_uncompressed adds sum_i bit_i(r) 2^i R to the hash, with R the
;     randomizer generator (hash_to_curve of "...{domain}.Randomizer") and
;     bit_i the 251 little-endian bits of the scalar r; that is r R;
;   - commit is the x-coordinate of commit_uncompressed.
;
; The generators are parameters (GENS, the list of G_w, and RGEN = R): they
; come from Blake2Xs hash-to-curve, which is not formalised.  The functions
; are defined for every parameter; the result is in the subgroup when the
; parameters are (hbhp-gens-okp).  The network instances (mainnet, testnet
; and canary v0) are BHP256 = (3, 57), BHP512 = (6, 43), BHP768 = (15, 23),
; BHP1024 = (8, 54) with domains "AleoBHP256", "AleoBHP512", "AleoBHP768",
; "AleoBHP1024" (console/network/src/mainnet_v0.rs); their generators are
; the constrained functions hbhp-setup-gens and hbhp-setup-random-base.

(in-package "ALEOVM")

(include-book "kestrel/fty/defresult" :dir :system)
(include-book "kestrel/utilities/bits-as-digits" :dir :system)
(include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system)
(include-book "projects/bls12-377-curves/ecurve/edwards-bls12" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "../edwards-order/bls12-points"))
(local (include-book "../edwards-assoc/edwards-bls12-associativity"))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "kestrel/arithmetic-light/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Subgroup closure.

(local
 (defruled hbhp-curve-facts
   (and (ecurve::twisted-edwards-curve-completep (ecurve::edwards-bls12-curve))
        (dm::primep (ecurve::edwards-bls12-r)))
   :enable (ecurve::edwards-bls12-curve-completep)))

(local
 (defun hbhp-nat-induct (n)
   (if (zp n) n (hbhp-nat-induct (1- n)))))

(local
 (defruled hbhp-mul-distrib-nat
   (implies (and (ecurve::edwards-bls12-pointp p1)
                 (ecurve::edwards-bls12-pointp p2)
                 (natp n))
            (equal (ecurve::edwards-bls12-mul n (ecurve::edwards-bls12-add p1 p2))
                   (ecurve::edwards-bls12-add (ecurve::edwards-bls12-mul n p1)
                                              (ecurve::edwards-bls12-mul n p2))))
   :induct (hbhp-nat-induct n)
   :hints (("Subgoal *1/1"
            :in-theory (enable ecurve::edwards-bls12-add ecurve::edwards-bls12-mul
                               (:e ecurve::twisted-edwards-add)
                               (:e ecurve::edwards-bls12-curve)))
           ("Subgoal *1/2"
            :use ((:instance ecurve::twisted-edwards-mul-succ
                             (n (1- n)) (curve (ecurve::edwards-bls12-curve))
                             (point (ecurve::edwards-bls12-add p1 p2)))
                  (:instance ecurve::twisted-edwards-mul-succ
                             (n (1- n)) (curve (ecurve::edwards-bls12-curve))
                             (point p1))
                  (:instance ecurve::twisted-edwards-mul-succ
                             (n (1- n)) (curve (ecurve::edwards-bls12-curve))
                             (point p2))
                  (:instance ecurve::edwards-bls12-add-associative
                             (point1 p1) (point2 p2)
                             (point3 (ecurve::edwards-bls12-add
                                      (ecurve::edwards-bls12-mul (1- n) p1)
                                      (ecurve::edwards-bls12-mul (1- n) p2))))
                  (:instance ecurve::edwards-bls12-add-associative
                             (point1 p2)
                             (point2 (ecurve::edwards-bls12-mul (1- n) p1))
                             (point3 (ecurve::edwards-bls12-mul (1- n) p2)))
                  (:instance ecurve::edwards-bls12-add-associative
                             (point1 (ecurve::edwards-bls12-mul (1- n) p1))
                             (point2 p2)
                             (point3 (ecurve::edwards-bls12-mul (1- n) p2)))
                  (:instance ecurve::edwards-bls12-add-associative
                             (point1 p1)
                             (point2 (ecurve::edwards-bls12-mul (1- n) p1))
                             (point3 (ecurve::edwards-bls12-add
                                      p2 (ecurve::edwards-bls12-mul (1- n) p2))))
                  (:instance ecurve::twisted-edwards-add-commutative
                             (point1 p2)
                             (point2 (ecurve::edwards-bls12-mul (1- n) p1))
                             (curve (ecurve::edwards-bls12-curve)))
                  hbhp-curve-facts)
            :in-theory (e/d (ecurve::edwards-bls12-add ecurve::edwards-bls12-mul
                             ecurve::edwards-bls12-pointp)
                            (ecurve::edwards-bls12-add-associative
                             ecurve::twisted-edwards-add-commutative))))))

(local
 (defruled hbhp-r-pointp-when-r-kills
   (implies (and (ecurve::edwards-bls12-pointp p1)
                 (equal (ecurve::edwards-bls12-mul (ecurve::edwards-bls12-r) p1)
                        (ecurve::twisted-edwards-zero)))
            (ecurve::edwards-bls12-r-pointp p1))
   :use (hbhp-curve-facts
         (:instance ecurve::twisted-edwards-point-orderp-when-prime-kills
                    (point p1) (r (ecurve::edwards-bls12-r))
                    (curve (ecurve::edwards-bls12-curve))))
   :enable (ecurve::edwards-bls12-r-pointp ecurve::edwards-bls12-mul
            ecurve::edwards-bls12-pointp)))

(local
 (defruled hbhp-r-kills-r-point
   (implies (ecurve::edwards-bls12-r-pointp p1)
            (equal (ecurve::edwards-bls12-mul (ecurve::edwards-bls12-r) p1)
                   (ecurve::twisted-edwards-zero)))
   :enable (ecurve::edwards-bls12-r-pointp ecurve::edwards-bls12-mul
            ecurve::twisted-edwards-point-orderp)))

(defrule hbhp-r-pointp-of-add
  (implies (and (ecurve::edwards-bls12-r-pointp p1)
                (ecurve::edwards-bls12-r-pointp p2))
           (ecurve::edwards-bls12-r-pointp (ecurve::edwards-bls12-add p1 p2)))
  :use ((:instance hbhp-mul-distrib-nat (n (ecurve::edwards-bls12-r)))
        (:instance hbhp-r-pointp-when-r-kills
                   (p1 (ecurve::edwards-bls12-add p1 p2)))
        (:instance hbhp-r-kills-r-point (p1 p1))
        (:instance hbhp-r-kills-r-point (p1 p2)))
  :enable ((:e ecurve::edwards-bls12-add) (:e ecurve::twisted-edwards-zero)))

(defrule hbhp-r-pointp-of-mul
  (implies (ecurve::edwards-bls12-r-pointp p1)
           (ecurve::edwards-bls12-r-pointp (ecurve::edwards-bls12-mul k p1)))
  :use ((:instance hbhp-r-pointp-when-r-kills
                   (p1 (ecurve::edwards-bls12-mul k p1)))
        (:instance hbhp-r-kills-r-point (p1 p1))
        (:instance ecurve::twisted-edwards-mul-of-mul
                   (ecurve::scalar (ecurve::edwards-bls12-r))
                   (ecurve::scalar1 (ifix k)) (ecurve::point p1)
                   (ecurve::curve (ecurve::edwards-bls12-curve)))
        (:instance ecurve::twisted-edwards-mul-of-mul
                   (ecurve::scalar (ifix k))
                   (ecurve::scalar1 (ecurve::edwards-bls12-r)) (ecurve::point p1)
                   (ecurve::curve (ecurve::edwards-bls12-curve)))
        (:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp
                   (ecurve::x p1))
        hbhp-curve-facts)
  :enable (ecurve::edwards-bls12-mul ecurve::edwards-bls12-pointp)
  :disable (ecurve::twisted-edwards-mul-of-mul
            ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp))

(defrule hbhp-r-pointp-of-zero
  (ecurve::edwards-bls12-r-pointp (ecurve::twisted-edwards-zero))
  :enable ecurve::edwards-bls12-r-pointp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parameters.

(define hbhp-r-point-listp (gens)
  :verify-guards nil
  :returns (yes/no booleanp)
  (if (atom gens)
      (null gens)
    (and (ecurve::edwards-bls12-r-pointp (car gens))
         (hbhp-r-point-listp (cdr gens)))))

(define hbhp-nonzero-listp (gens)
  :verify-guards nil
  :returns (yes/no booleanp)
  (if (atom gens)
      t
    (and (not (equal (car gens) (ecurve::twisted-edwards-zero)))
         (hbhp-nonzero-listp (cdr gens)))))

(define hbhp-gens-okp (gens)
  :verify-guards nil
  :returns (yes/no booleanp)
  :short "Well-formed window generators: subgroup points, none zero."
  (and (consp gens)
       (hbhp-r-point-listp gens)
       (hbhp-nonzero-listp gens)))

(define hbhp-data-bits ()
  :returns (n posp)
  :short "Field::size_in_data_bits for the BLS12-377 base field."
  252)

(define hbhp-domain-size ()
  :returns (n posp)
  :short "Bits of the domain: data bits minus the 64 bits of the length."
  188)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BHPHasher.

(define hbhp-chunk-scalar ((b0 bitp) (b1 bitp) (b2 bitp))
  :returns (k integerp)
  :short "The lookup multiplier of a 3-bit chunk: @($\\pm(1 + b_0 + 2 b_1)$)."
  (b* ((m (+ 1 (acl2::bfix b0) (* 2 (acl2::bfix b1)))))
    (if (equal b2 1) (- m) m)))

(define hbhp-window-scalar ((bits bit-listp) (j natp))
  :verify-guards nil
  :returns (k integerp)
  :short "Scalar of the chunks of a window starting at chunk position @('j')."
  :measure (len bits)
  (if (< (len bits) 3)
      0
    (+ (* (hbhp-chunk-scalar (first bits) (second bits) (third bits))
          (expt 16 (lnfix j)))
       (hbhp-window-scalar (nthcdr 3 bits) (1+ (lnfix j))))))

(define hbhp-pad ((bits bit-listp))
  :verify-guards nil
  :returns (padded bit-listp :hyp :guard)
  :short "Pad with zeros to a multiple of 3 bits."
  (append bits (repeat (mod (- (len bits)) 3) 0)))

(define hbhp-hasher-sum ((bits bit-listp) gens (w posp) acc)
  :verify-guards nil
  :short "Fold of @('acc') with @($s_w G_w$) over the windows of @('bits')."
  :measure (len bits)
  (b* ((w (acl2::pos-fix w))
       ((when (or (endp bits) (endp gens))) acc)
       (n (min (* 3 w) (len bits)))
       (s (hbhp-window-scalar (take n bits) 0)))
    (hbhp-hasher-sum (nthcdr n bits) (cdr gens) w
                     (ecurve::edwards-bls12-add
                      acc (ecurve::edwards-bls12-mul s (car gens))))))

(define hbhp-hasher-hash-uncompressed (gens (w posp) (bits bit-listp))
  :verify-guards nil
  :short "@('BHPHasher::hash_uncompressed'): a point, or an error when the
          input length is out of range."
  (b* ((w (acl2::pos-fix w))
       (n (len bits))
       ((when (or (<= n (* 3 w))
                  (> n (* 3 w (len gens)))))
        (reserr nil)))
    (hbhp-hasher-sum (hbhp-pad bits) gens w (ecurve::twisted-edwards-zero))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; BHP.

(define hbhp-bytes-to-bits-le ((bytes nat-listp))
  :verify-guards nil
  :returns (bits bit-listp)
  (if (endp bytes)
      nil
    (append (acl2::nat=>lebits 8 (car bytes))
            (hbhp-bytes-to-bits-le (cdr bytes)))))

(define hbhp-char-codes ((chars character-listp))
  :returns (codes nat-listp)
  (if (endp chars)
      nil
    (cons (char-code (car chars)) (hbhp-char-codes (cdr chars)))))

(define hbhp-domain-bits ((domain stringp))
  :verify-guards nil
  :returns (bits bit-listp)
  :short "@('BHP::setup'): the bytes of the domain as little-endian bits,
          resized to 188 bits and reversed."
  (b* ((bits (hbhp-bytes-to-bits-le (hbhp-char-codes (coerce (if (stringp domain) domain "") (quote list)))))
       (n (hbhp-domain-size))
       (bits (if (<= n (len bits))
                 (take n bits)
               (append bits (repeat (- n (len bits)) 0)))))
    (rev bits)))

(define hbhp-domain-okp ((domain stringp))
  :verify-guards nil
  :returns (yes/no booleanp)
  :short "@('BHP::setup') accepts at most 188 bits of domain."
  (<= (* 8 (length (if (stringp domain) domain ""))) (hbhp-domain-size)))

(define hbhp-digest-bits (digest)
  :verify-guards nil
  :returns (bits bit-listp)
  :short "The first 252 of the 253 little-endian bits of the x-coordinate."
  (take (hbhp-data-bits)
        (acl2::nat=>lebits 253 (nfix (ecurve::point-finite->x digest)))))

(define hbhp-hash-iter (gens (w posp) (max posp) (rest bit-listp) digest)
  :verify-guards nil
  :short "The iterations after the first of @('BHP::hash_uncompressed')."
  :measure (len rest)
  (b* (((when (endp rest)) digest)
       (max (acl2::pos-fix max))
       (n (min max (len rest)))
       (pre (append (hbhp-digest-bits digest) (take n rest)))
       (next (hbhp-hasher-hash-uncompressed gens w pre))
       ((when (reserrp next)) next))
    (hbhp-hash-iter gens w max (nthcdr n rest) next)))

(define hbhp-max-bits-per-iteration (gens (w posp))
  :verify-guards nil
  :returns (n integerp)
  (- (* 3 (acl2::pos-fix w) (len gens)) (hbhp-data-bits)))

(define hbhp-hash-uncompressed ((domain stringp) gens (w posp) (bits bit-listp))
  :verify-guards nil
  :short "@('BHP::hash_uncompressed')."
  (b* ((w (acl2::pos-fix w))
       (max (hbhp-max-bits-per-iteration gens w))
       ((unless (and (hbhp-domain-okp domain) (< 0 max))) (reserr nil))
       ((when (endp bits)) (ecurve::twisted-edwards-zero))
       (n (min max (len bits)))
       (pre (append (hbhp-domain-bits domain)
                    (acl2::nat=>lebits 64 (mod (len bits) (expt 2 64)))
                    (take n bits)))
       (first (hbhp-hasher-hash-uncompressed gens w pre))
       ((when (reserrp first)) first))
    (hbhp-hash-iter gens w max (nthcdr n bits) first)))

(define hbhp-hash ((domain stringp) gens (w posp) (bits bit-listp))
  :verify-guards nil
  :short "@('BHP::hash'): the x-coordinate of @(tsee hbhp-hash-uncompressed)."
  (b* ((h (hbhp-hash-uncompressed domain gens w bits))
       ((when (reserrp h)) h))
    (ecurve::point-finite->x h)))

(define hbhp-commit-uncompressed ((domain stringp) gens (w posp) rgen
                                  (bits bit-listp) (r natp))
  :verify-guards nil
  :short "@('BHP::commit_uncompressed'): the hash plus @($r R$)."
  (b* ((h (hbhp-hash-uncompressed domain gens w bits))
       ((when (reserrp h)) h))
    (ecurve::edwards-bls12-add h (ecurve::edwards-bls12-mul (lnfix r) rgen))))

(define hbhp-commit ((domain stringp) gens (w posp) rgen (bits bit-listp) (r natp))
  :verify-guards nil
  :short "@('BHP::commit'): the x-coordinate of @(tsee hbhp-commit-uncompressed)."
  (b* ((c (hbhp-commit-uncompressed domain gens w rgen bits r))
       ((when (reserrp c)) c))
    (ecurve::point-finite->x c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Result types.

(defrule hbhp-r-pointp-of-hasher-sum
  (implies (and (hbhp-r-point-listp gens)
                (ecurve::edwards-bls12-r-pointp acc))
           (ecurve::edwards-bls12-r-pointp (hbhp-hasher-sum bits gens w acc)))
  :induct (hbhp-hasher-sum bits gens w acc)
  :enable (hbhp-hasher-sum hbhp-r-point-listp))

;; HBHP-OKRESP: an error, or a subgroup point.

(define hbhp-okresp (x)
  :returns (yes/no booleanp)
  (or (reserrp x)
      (ecurve::edwards-bls12-r-pointp x)))

(defruled hbhp-r-pointp-when-okresp
  (implies (and (hbhp-okresp x) (not (reserrp x)))
           (ecurve::edwards-bls12-r-pointp x))
  :enable hbhp-okresp)

(defrule hbhp-okresp-when-r-pointp
  (implies (ecurve::edwards-bls12-r-pointp x)
           (hbhp-okresp x))
  :enable hbhp-okresp)

(defrule hbhp-okresp-of-reserr
  (hbhp-okresp (reserr x))
  :enable hbhp-okresp)

(defrule hbhp-hasher-hash-uncompressed-type
  (implies (hbhp-r-point-listp gens)
           (hbhp-okresp (hbhp-hasher-hash-uncompressed gens w bits)))
  :enable hbhp-hasher-hash-uncompressed)

(defrule hbhp-hash-iter-type
  (implies (and (hbhp-r-point-listp gens)
                (ecurve::edwards-bls12-r-pointp digest))
           (hbhp-okresp (hbhp-hash-iter gens w max rest digest)))
  :induct (hbhp-hash-iter gens w max rest digest)
  :enable (hbhp-hash-iter hbhp-r-pointp-when-okresp))

(defrule hbhp-hash-uncompressed-type
  (implies (hbhp-r-point-listp gens)
           (hbhp-okresp (hbhp-hash-uncompressed domain gens w bits)))
  :enable (hbhp-hash-uncompressed hbhp-r-pointp-when-okresp))

(defrule hbhp-commit-uncompressed-type
  (implies (and (hbhp-r-point-listp gens)
                (ecurve::edwards-bls12-r-pointp rgen))
           (hbhp-okresp (hbhp-commit-uncompressed domain gens w rgen bits r)))
  :enable (hbhp-commit-uncompressed hbhp-r-pointp-when-okresp))

;;;;;;;;

;; Network instances (BHP256, BHP512, BHP768, BHP1024).

(define hbhp-size-num-windows ((size natp))
  :returns (nw posp)
  (case size (256 3) (512 6) (768 15) (1024 8) (otherwise 3)))

(define hbhp-size-window-size ((size natp))
  :returns (w posp)
  (case size (256 57) (512 43) (768 23) (1024 54) (otherwise 57)))

(define hbhp-size-domain ((size natp))
  :returns (domain stringp)
  (case size
    (256 "AleoBHP256") (512 "AleoBHP512") (768 "AleoBHP768") (1024 "AleoBHP1024")
    (otherwise "AleoBHP256")))

(local
 (defruled hbhp-r-pointp-of-bls12-order-g
   (ecurve::edwards-bls12-r-pointp (ecurve::bls12-order-g))
   :use (:instance hbhp-r-pointp-when-r-kills (p1 (ecurve::bls12-order-g)))
   :enable (ecurve::edwards-bls12-mul ecurve::edwards-bls12-pointp)))

(local
 (defun hbhp-repeat-g (n)
   (if (zp n) nil (cons (ecurve::bls12-order-g) (hbhp-repeat-g (1- n))))))

(encapsulate
  (((hbhp-setup-gens *) => * :formals (size) :guard t)
   ((hbhp-setup-random-base *) => * :formals (size) :guard t))

  (local (defun hbhp-setup-gens (size)
           (hbhp-repeat-g (hbhp-size-num-windows size))))
  (local (defun hbhp-setup-random-base (size)
           (declare (ignore size))
           (ecurve::bls12-order-g)))

  (local
   (defrule hbhp-repeat-g-props
     (and (hbhp-r-point-listp (hbhp-repeat-g n))
          (hbhp-nonzero-listp (hbhp-repeat-g n))
          (equal (len (hbhp-repeat-g n)) (nfix n)))
     :enable (hbhp-r-point-listp hbhp-nonzero-listp hbhp-r-pointp-of-bls12-order-g)))

  (defrule hbhp-gens-okp-of-setup-gens
    (hbhp-gens-okp (hbhp-setup-gens size))
    :enable hbhp-gens-okp
    :expand ((hbhp-repeat-g (hbhp-size-num-windows size))))

  (defrule hbhp-len-of-setup-gens
    (equal (len (hbhp-setup-gens size)) (hbhp-size-num-windows size)))

  (defrule hbhp-r-pointp-of-setup-random-base
    (ecurve::edwards-bls12-r-pointp (hbhp-setup-random-base size))
    :enable hbhp-r-pointp-of-bls12-order-g)

  (defrule hbhp-setup-random-base-nonzero
    (not (equal (hbhp-setup-random-base size) (ecurve::twisted-edwards-zero)))))

(defrule hbhp-r-point-listp-of-setup-gens
  (hbhp-r-point-listp (hbhp-setup-gens size))
  :use hbhp-gens-okp-of-setup-gens
  :in-theory (e/d (hbhp-gens-okp) (hbhp-gens-okp-of-setup-gens)))

(define hbhp-bhp-hash-uncompressed ((size natp) (bits bit-listp))
  :verify-guards nil
  :short "Replacement for the @('bhp-hash-uncompressed') stub of base.lisp:
          the network BHP instance of the given size.  The error case does
          not arise for these instances (the zero point is returned there)."
  (b* ((h (hbhp-hash-uncompressed (hbhp-size-domain size)
                                  (hbhp-setup-gens size)
                                  (hbhp-size-window-size size)
                                  bits)))
    (if (reserrp h) (ecurve::twisted-edwards-zero) h)))

(define hbhp-bhp-hash ((size natp) (bits bit-listp))
  :verify-guards nil
  :short "@('BHP::hash') at a network instance: the x-coordinate of
          @(tsee hbhp-bhp-hash-uncompressed)."
  (ecurve::point-finite->x (hbhp-bhp-hash-uncompressed size bits)))

(define hbhp-bhp-commit-uncompressed ((size natp) (bits bit-listp) randomizer)
  :verify-guards nil
  :short "Replacement for the @('bhp-commit-uncompressed') stub of base.lisp."
  (b* ((c (hbhp-commit-uncompressed (hbhp-size-domain size)
                                    (hbhp-setup-gens size)
                                    (hbhp-size-window-size size)
                                    (hbhp-setup-random-base size)
                                    bits
                                    (nfix randomizer))))
    (if (reserrp c) (ecurve::twisted-edwards-zero) c)))

(define hbhp-bhp-commit ((size natp) (bits bit-listp) randomizer)
  :verify-guards nil
  :short "@('BHP::commit') at a network instance: the x-coordinate of
          @(tsee hbhp-bhp-commit-uncompressed)."
  (ecurve::point-finite->x (hbhp-bhp-commit-uncompressed size bits randomizer)))

(defrule hbhp-r-pointp-of-bhp-hash-uncompressed
  (ecurve::edwards-bls12-r-pointp (hbhp-bhp-hash-uncompressed size bits))
  :enable (hbhp-bhp-hash-uncompressed hbhp-r-pointp-when-okresp))

(defrule hbhp-r-pointp-of-bhp-commit-uncompressed
  (ecurve::edwards-bls12-r-pointp (hbhp-bhp-commit-uncompressed size bits randomizer))
  :enable (hbhp-bhp-commit-uncompressed hbhp-r-pointp-when-okresp))
