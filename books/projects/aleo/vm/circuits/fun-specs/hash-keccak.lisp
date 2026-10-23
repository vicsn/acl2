; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Keccak and SHA-3 as snarkVM computes them (commit 7dc117d45).
;
; console/algorithms/src/keccak: Keccak<TYPE, VARIANT>::hash packs the input
; bits into bytes little-endian (bytes_from_bits_le, zero-filling the last
; byte), runs tiny_keccak's Keccak-VARIANT (TYPE 0) or SHA3-VARIANT (TYPE 1),
; and unpacks the digest bytes little-endian.  On bits this is the FIPS 202
; sponge of kestrel/crypto/sha-3 applied to the input padded with zeros to a
; whole number of bytes, with the SHA-3 domain suffix 01 for TYPE 1.  That is
; HKEC-KECCAK-FAMILY-HASH, the concrete version of KECCAK-FAMILY-HASH in
; base.lisp, with VARIANT the pair (TYPE . VARIANT).
;
; The rest of the book follows circuit/algorithms/src/keccak/hash.rs, which
; computes the same hash on Boolean wires: the state is 25 lanes of 64
; little-endian bits (lane x + 5y), and HKEC-ROUND, HKEC-PERMUTATION-F,
; HKEC-ROTATE-LEFT, HKEC-PAD-KECCAK and HKEC-PAD-SHA3 are the functions of the
; same names there.  fun-circuits/hkec-sha3.lisp proves them equal to the
; kestrel/crypto/sha-3 round, Keccak-f[1600] and pad10*1, and HKEC-SPONGE
; equal to HKEC-KECCAK-FAMILY-HASH.

(in-package "ALEOVM")

(include-book "kestrel/crypto/sha-3/sha-3" :dir :system)
(include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(set-verify-guards-eagerness 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Variants.

(define hkec-variant-p (variant)
  :returns (yes/no booleanp)
  :short "snarkVM's Keccak instances: (TYPE . VARIANT), TYPE 0 Keccak, 1 SHA-3."
  (and (consp variant)
       (member-equal (car variant) '(0 1))
       (member-equal (cdr variant) '(224 256 384 512))
       t))

(define hkec-variant-type (variant)
  (if (consp variant) (car variant) 0))

(define hkec-variant-bits (variant)
  :returns (d natp)
  (if (consp variant) (nfix (cdr variant)) 0))

(define hkec-bitrate ((d natp))
  :verify-guards nil
  :returns (r integerp)
  :short "PERMUTATION_WIDTH - 2 * VARIANT."
  (- 1600 (* 2 (nfix d))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The console hash.

(define hkec-byte-pad ((bits true-listp))
  :verify-guards nil
  :short "bits_from_bytes_le (bytes_from_bits_le bits): zero-fill to a byte."
  (append bits (acl2::repeat (mod (- (len bits)) 8) 0)))

(define hkec-keccak-family-hash (variant (input-bits true-listp))
  :short "Keccak<TYPE, VARIANT>::hash of console/algorithms/src/keccak."
  :verify-guards nil
  (b* ((d (hkec-variant-bits variant))
       (m (hkec-byte-pad input-bits)))
    (if (not (hkec-variant-p variant))
        nil
      (if (equal (hkec-variant-type variant) 0)
          (sha3::keccak (* 2 d) m d)
        (sha3::keccak (* 2 d) (append m '(0 1)) d)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bits and lanes.

(defun hkec-bnot (a)
  (declare (xargs :guard t))
  (acl2::bitxor a 1))

(defun hkec-lane-xor (xs ys)
  (declare (xargs :guard (and (true-listp xs) (true-listp ys))))
  (if (endp xs)
      nil
    (cons (acl2::bitxor (car xs) (car ys))
          (hkec-lane-xor (cdr xs) (cdr ys)))))

(defun hkec-lane-chi (as bs cs)
  (declare (xargs :guard (and (true-listp as) (true-listp bs) (true-listp cs))))
  (if (endp as)
      nil
    (cons (acl2::bitxor (car as)
                        (acl2::bitand (hkec-bnot (car bs)) (car cs)))
          (hkec-lane-chi (cdr as) (cdr bs) (cdr cs)))))

(defun hkec-rotate-left (bits n)
  (declare (xargs :guard (and (true-listp bits) (natp n))))
  ;; Vec::rotate_left on the bits of a U64, then U64::from_bits_le.
  (append (nthcdr n bits) (take n bits)))

(defun hkec-flatten (lanes)
  (declare (xargs :guard (true-list-listp lanes)))
  ;; write_bits_le of each lane in turn
  (if (endp lanes)
      nil
    (append (car lanes) (hkec-flatten (cdr lanes)))))

(defun hkec-nat-bits (n k)
  (declare (xargs :guard (and (natp n) (natp k))))
  (if (zp k)
      nil
    (cons (mod (nfix n) 2) (hkec-nat-bits (floor (nfix n) 2) (1- k)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Constants (keccak/mod.rs).

(defconst *hkec-round-constants*
  '(#x0000000000000001 #x0000000000008082 #x800000000000808A #x8000000080008000
    #x000000000000808B #x0000000080000001 #x8000000080008081 #x8000000000008009
    #x000000000000008A #x0000000000000088 #x0000000080008009 #x000000008000000A
    #x000000008000808B #x800000000000008B #x8000000000008089 #x8000000000008003
    #x8000000000008002 #x8000000000000080 #x000000000000800A #x800000008000000A
    #x8000000080008081 #x8000000000008080 #x0000000080000001 #x8000000080008008))

(defun hkec-nat-bits-list (ns)
  (declare (xargs :guard (nat-listp ns)))
  (if (endp ns)
      nil
    (cons (hkec-nat-bits (car ns) 64) (hkec-nat-bits-list (cdr ns)))))

(defconst *hkec-round-constant-bits*
  (hkec-nat-bits-list *hkec-round-constants*))

(defun hkec-rotl-offsets-aux (tt x y rotl)
  (declare (xargs :measure (nfix (- 24 tt))
                  :guard (and (natp tt) (natp x) (natp y) (true-listp rotl))))
  (if (or (not (natp tt)) (>= tt 24))
      rotl
    (let ((rotr (mod (floor (* (+ tt 1) (+ tt 2)) 2) 64)))
      (hkec-rotl-offsets-aux (+ tt 1)
                             y
                             (mod (+ (* 2 (nfix x)) (* 3 (nfix y))) 5)
                             (update-nth (+ (nfix x) (* 5 (nfix y)))
                                         (mod (- 64 rotr) 64)
                                         rotl)))))

(defconst *hkec-rotl*
  ;; Keccak::rotl_offsets
  (hkec-rotl-offsets-aux 0 1 0 (acl2::repeat 25 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The round function (Keccak::round).  A state is a list of 25 lanes.

(defun hkec-theta-c-lane (a x)
  (declare (xargs :guard (and (true-list-listp a) (natp x))))
  (hkec-lane-xor
   (hkec-lane-xor
    (hkec-lane-xor
     (hkec-lane-xor (nth x a) (nth (+ x 5) a))
     (nth (+ x 10) a))
    (nth (+ x 15) a))
   (nth (+ x 20) a)))

(defun hkec-theta-c (a)
  (declare (xargs :guard (true-list-listp a)))
  (list (hkec-theta-c-lane a 0)
        (hkec-theta-c-lane a 1)
        (hkec-theta-c-lane a 2)
        (hkec-theta-c-lane a 3)
        (hkec-theta-c-lane a 4)))

(defun hkec-theta-d-lane (c x)
  (declare (xargs :guard (and (true-list-listp c) (natp x))))
  (hkec-lane-xor (nth (mod (+ x 4) 5) c)
                 (hkec-rotate-left (nth (mod (+ x 1) 5) c) 63)))

(defun hkec-theta-d (c)
  (declare (xargs :guard (true-list-listp c)))
  (list (hkec-theta-d-lane c 0)
        (hkec-theta-d-lane c 1)
        (hkec-theta-d-lane c 2)
        (hkec-theta-d-lane c 3)
        (hkec-theta-d-lane c 4)))

(defun hkec-theta-apply (a d i)
  (declare (xargs :guard (and (true-list-listp a) (true-list-listp d) (natp i))
                  :measure (nfix (- 25 i))))
  ;; a_1[x + 5y] = a[x + 5y] ^ d[x]
  (if (or (not (natp i)) (>= i 25))
      nil
    (cons (hkec-lane-xor (nth i a) (nth (mod i 5) d))
          (hkec-theta-apply a d (+ i 1)))))

(defun hkec-theta (a)
  (declare (xargs :guard (true-list-listp a)))
  (hkec-theta-apply a (hkec-theta-d (hkec-theta-c a)) 0))

(defun hkec-rho-pi-aux (i a1 a2)
  (declare (xargs :guard (and (natp i) (true-listp a1) (true-listp a2))
                  :measure (nfix (- 25 i))))
  ;; a_2[y + ((2x + 3y) mod 5) * 5] = rotate_left(a_1[x + 5y], rotl[x + 5y])
  (if (or (not (natp i)) (>= i 25))
      a2
    (let ((x (mod i 5))
          (y (floor i 5)))
      (hkec-rho-pi-aux (+ i 1)
                       a1
                       (update-nth (+ y (* 5 (mod (+ (* 2 x) (* 3 y)) 5)))
                                   (hkec-rotate-left (nth i a1)
                                                     (nth i *hkec-rotl*))
                                   a2)))))

(defun hkec-rho-pi (a1)
  (declare (xargs :guard (true-listp a1)))
  (hkec-rho-pi-aux 0 a1 (acl2::repeat 25 nil)))

(defun hkec-chi-aux (a2 i)
  (declare (xargs :guard (and (true-list-listp a2) (natp i))
                  :measure (nfix (- 25 i))))
  ;; a_3[x + 5y] = a[x, y] ^ (!a[x+1, y] & a[x+2, y])
  (if (or (not (natp i)) (>= i 25))
      nil
    (let ((x (mod i 5))
          (y (floor i 5)))
      (cons (hkec-lane-chi (nth i a2)
                           (nth (+ (mod (+ x 1) 5) (* 5 y)) a2)
                           (nth (+ (mod (+ x 2) 5) (* 5 y)) a2))
            (hkec-chi-aux a2 (+ i 1))))))

(defun hkec-chi (a2)
  (declare (xargs :guard (true-list-listp a2)))
  (hkec-chi-aux a2 0))

(defun hkec-iota (a3 rc)
  (declare (xargs :guard (and (true-list-listp a3) (true-listp rc))))
  (update-nth 0 (hkec-lane-xor (nth 0 a3) rc) a3))

(define hkec-round ((a true-list-listp) (rc true-listp))
  :short "Keccak::round: iota of chi of rho-pi of theta, for round constant bits @('rc')."
  :verify-guards nil
  (hkec-iota (hkec-chi (hkec-rho-pi (hkec-theta a))) rc))

(define hkec-rounds ((a true-list-listp) (rcs true-list-listp))
  :verify-guards nil
  (if (endp rcs)
      a
    (hkec-rounds (hkec-round a (car rcs)) (cdr rcs))))

(define hkec-permutation-f ((s true-listp))
  :short "Keccak::permutation_f on 1600 bits: 24 rounds over the 64-bit lanes."
  :verify-guards nil
  (hkec-flatten (hkec-rounds (acl2::group 64 s) *hkec-round-constant-bits*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Padding (Keccak::pad_keccak, Keccak::pad_sha3).

(defun hkec-pos (r)
  (declare (xargs :guard t))
  (if (posp r) r 1))

(define hkec-pad-keccak ((input true-listp) (r posp))
  :short "M || 0* to a byte, then 1 0* 1 to a multiple of r, in r-bit blocks."
  :verify-guards nil
  (b* ((m (hkec-byte-pad input))
       (p (append m
                  '(1)
                  (acl2::repeat (mod (- (- (hkec-pos r) 1) (+ (len m) 1)) (hkec-pos r)) 0)
                  '(1))))
    (acl2::group (hkec-pos r) p)))

(define hkec-pad-sha3 ((input true-listp) (r posp))
  :short "M || 0* to a byte, then 0 1 1 0 0* 1 to a multiple of r, in r-bit blocks."
  :verify-guards nil
  (b* ((m (hkec-byte-pad input))
       (p (append m
                  '(0 1 1 0)
                  (acl2::repeat (mod (- (- (hkec-pos r) 1) (+ (len m) 4)) (hkec-pos r)) 0)
                  '(1))))
    (acl2::group (hkec-pos r) p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The sponge (Keccak::hash of circuit/algorithms/src/keccak/hash.rs).

(defun hkec-xor-prefix (s block)
  (declare (xargs :guard (and (true-listp s) (true-listp block))))
  ;; s[j] = s[j] ^ block[j] for j < |block|
  (if (endp block)
      s
    (cons (acl2::bitxor (car s) (car block))
          (hkec-xor-prefix (cdr s) (cdr block)))))

(define hkec-absorb ((s true-listp) (blocks true-list-listp))
  :verify-guards nil
  (if (endp blocks)
      s
    (hkec-absorb (hkec-permutation-f (hkec-xor-prefix s (car blocks)))
                 (cdr blocks))))

(define hkec-sponge (variant (input true-listp))
  :short "Keccak::hash on bits, for a valid variant (bitrate >= VARIANT, so no squeeze round)."
  :verify-guards nil
  (b* ((d (hkec-variant-bits variant))
       (r (hkec-bitrate d))
       ((unless (hkec-variant-p variant)) nil)
       (blocks (if (equal (hkec-variant-type variant) 0)
                   (hkec-pad-keccak input r)
                 (hkec-pad-sha3 input r)))
       (s (hkec-absorb (acl2::repeat 1600 0) blocks)))
    (take d (take r s))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The constraint that base.lisp states for KECCAK-FAMILY-HASH.

(defrule hkec-bit-listp-when-sha3-bit-stringp
  (implies (sha3::bit-stringp x)
           (bit-listp x))
  :induct (len x)
  :enable (sha3::bit-stringp bit-listp acl2::all-unsigned-byte-p bitp unsigned-byte-p))

(defrule bit-listp-of-hkec-keccak-family-hash
  (bit-listp (hkec-keccak-family-hash variant input-bits))
  :enable (hkec-keccak-family-hash hkec-variant-p hkec-variant-bits)
  :disable sha3::bit-stringp
  :use ((:instance sha3::bit-stringp-of-keccak
                   (c (* 2 (hkec-variant-bits variant)))
                   (n (hkec-byte-pad input-bits))
                   (d (hkec-variant-bits variant)))
        (:instance sha3::bit-stringp-of-keccak
                   (c (* 2 (hkec-variant-bits variant)))
                   (n (append (hkec-byte-pad input-bits) '(0 1)))
                   (d (hkec-variant-bits variant)))))

(defrule len-of-hkec-keccak-family-hash
  (implies (hkec-variant-p variant)
           (equal (len (hkec-keccak-family-hash variant input-bits))
                  (cdr variant)))
  :enable (hkec-keccak-family-hash hkec-variant-p hkec-variant-bits)
  :disable sha3::len-of-keccak
  :use ((:instance sha3::len-of-keccak
                   (c (* 2 (hkec-variant-bits variant)))
                   (n (hkec-byte-pad input-bits))
                   (d (hkec-variant-bits variant)))
        (:instance sha3::len-of-keccak
                   (c (* 2 (hkec-variant-bits variant)))
                   (n (append (hkec-byte-pad input-bits) '(0 1)))
                   (d (hkec-variant-bits variant)))))
