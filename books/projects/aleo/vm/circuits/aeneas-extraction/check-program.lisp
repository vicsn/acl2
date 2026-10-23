; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Extraction checks for circuit/program: the literal casts, the Identifier,
; ProgramID and DynamicFuture equalities, Record::is_hiding, the OutputID
; constructors and Literal::new. The gadgets' internal wires are fresh
; symbols, renamed onto the extracted wires; the unit wire u is 1.

(include-book "check-lib")
(include-book "../fun-circuits/prog-equal")
(include-book "../fun-circuits/prog-ids")
(include-book "../fun-circuits/progx-boolean-cast")
(include-book "../fun-circuits/progx-int-cast")
(include-book "../fun-circuits/literal-new-r1cs")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *u* '((u . 1)))

(defconst *r* (bits-lt-prime-rlen (base-prime)))

(defun lebits-lc (bits i)
  (declare (xargs :measure (len bits)))
  (if (atom bits) nil (cons (list (expt 2 i) (car bits)) (lebits-lc (cdr bits) (1+ i)))))

(defun sym-rows (prefix i n w)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons (gs (acl2::packn (list prefix i "_")) w)
          (sym-rows prefix (1+ i) (1- n) w))))

(defun wv-rows (lo n w)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil (cons (wvs lo w) (wv-rows (+ (nfix lo) (nfix w)) (1- n) w))))

; Type codes as in the harnesses: 0 address, 1 boolean, 2 field, 3 group,
; 4 integer of width w and signedness s, 5 scalar, 6 identifier literal.
(defun lit-type (k w s)
  (case k
    (0 (literal-type-address))
    (1 (literal-type-boolean))
    (2 (literal-type-field))
    (3 (literal-type-group))
    (5 (literal-type-scalar))
    (6 (literal-type-identifier))
    (t (case w
         (8 (if s (literal-type-i8) (literal-type-u8)))
         (16 (if s (literal-type-i16) (literal-type-u16)))
         (32 (if s (literal-type-i32) (literal-type-u32)))
         (64 (if s (literal-type-i64) (literal-type-u64)))
         (t (if s (literal-type-i128) (literal-type-u128)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Casts

(defun field-cast-g (to x tw)
  (b* ((g (gs "G" 13)) (z (gs "Z" 5)))
    (progx-field-cast-gadget
     to x
     (nth 0 g) (nth 1 g) (nth 2 g) (nth 3 g) (nth 4 g) (nth 5 g) (nth 6 g)
     (nth 7 g) (nth 8 g) (nth 9 g) (nth 10 g) (nth 11 g) (nth 12 g)
     (nth 0 z) (nth 1 z) (nth 2 z) (nth 3 z) (nth 4 z)
     (gs "I" tw)
     (gs "SX" 253) (gs "FR" 252) 'u (gs "SR" 250)
     (gs "RS" *r*) (sym-rows "BR" 0 31 8) (gs "EX" 5) (sym-rows "WR" 0 31 12)
     'partial 'uscore 'islet (base-prime))))

(defun cast-gadget (from fw fs to tw ts)
  (b* ((lt (lit-type to tw ts)))
    (case from
      (1 (progx-boolean-cast-gadget lt (wv 1) (gs "RS" *r*) 'u
                                    (sym-rows "BR" 0 31 8) (gs "EX" 5)
                                    (sym-rows "WR" 0 31 12)
                                    'partial 'uscore 'islet (base-prime)))
      (2 (field-cast-g lt (wv 1) tw))
      (4 (if (equal to 4)
             (progx-icast-int-gadget (wvs 1 fw) fs ts tw (base-prime))
           (and (not (member to '(2 5)))
                (field-cast-g lt 'xin tw))))
      (5 (cond ((equal to 4)
                (append (scalar-write-bits-le-gadget (wv 1) (gs "SB" 251) (gs "SBR" 250)
                                                     (base-prime))
                        (int-from-bits-le-gadget (nthcdr tw (gs "SB" 251)))))
               ((member to '(2 5)) nil)
               (t (field-cast-g lt (wv 1) tw))))
      (t (and (not (member to '(2 6)))
              (field-cast-g lt 'xin tw))))))

(defconst *int-types* '((8 nil) (16 nil) (32 nil) (64 nil) (128 nil)
                        (8 t) (16 t) (32 t) (64 t) (128 t)))

(defun cast-inputs (from fw)
  (case from (4 (wvs 1 fw)) (6 (wvs 1 248)) (t (list (wv 1)))))

(defun cast-subst (from fw)
  (append *u*
          (case from
            (4 (list (cons 'xin (lebits-lc (wvs 1 fw) 0))))
            (6 (list (cons 'xin (lebits-lc (wvs 1 248) 0))))
            (t nil))))

(defun cast-renamed-check (from fw fs to tw ts)
  (same-circuit-renamed (ext-run (acl2::circuits-h-p-cast *fuel* from fw fs to tw ts))
                        (cast-gadget from fw fs to tw ts)
                        (cast-inputs from fw)
                        (cast-subst from fw)))

; The Boolean destination: snarkVM computes is_one before is_zero, the
; gadget lists is_zero first. After the input wires: is_one's result and
; multiplier, is_zero's result and multiplier, the OR.
(defun boolean-dest-check (from fw fs)
  (b* ((k (len (cast-inputs from fw)))
       (x (if (member from '(4 6)) 'xin (wv 1))))
    (same-circuit-unordered
     (ext-run (acl2::circuits-h-p-cast *fuel* from fw fs 1 8 nil))
     (field-cast-to-boolean-gadget x (wv (+ k 4)) (wv (+ k 3)) (wv (+ k 2)) (wv (+ k 1))
                                   (wv (+ k 5)) (base-prime))
     (cast-subst from fw))))

; IdentifierLiteral to Scalar and Integer to IdentifierLiteral cast through
; to_field, which is Field::from_bits_le and caches the bits; the following
; Scalar::from_field or IdentifierLiteral::from_field reuses them. The
; gadgets decompose the field again with Field::to_bits_le.
(defun cached-bits-cast-p (from to)
  (or (and (equal from 6) (equal to 5))
      (and (equal from 4) (equal to 6))))

(defun cast-check (from fw fs to tw ts)
  (cond ((and (equal to 1) (not (equal from 1))) (boolean-dest-check from fw fs))
        ((cached-bits-cast-p from to) t)
        (t (cast-renamed-check from fw fs to tw ts))))

(defun cast-counts (from fw)
  (list (len (ext-run (acl2::circuits-h-p-cast *fuel* from fw nil (if (equal from 6) 5 6) 8 nil)))
        (len (cast-gadget from fw nil (if (equal from 6) 5 6) 8 nil))))

(defcheck identifier-literal-cast-scalar-differs
  (and (not (cast-renamed-check 6 0 nil 5 8 nil))
       (equal (cast-counts 6 0) '(247 759))))

(defun int-to-identifier-differs (ts)
  (if (atom ts)
      t
    (and (not (cast-renamed-check 4 (first (car ts)) (second (car ts)) 6 8 nil))
         (< (first (cast-counts 4 (first (car ts)))) (second (cast-counts 4 (first (car ts)))))
         (int-to-identifier-differs (cdr ts)))))

(defcheck integer-cast-identifier-literal-differs
  (and (int-to-identifier-differs *int-types*)
       (equal (cast-counts 4 8) '(22 1069))))

(defconst *non-int-dests* '(0 1 2 3 5 6))

; Every destination: the six non-integer ones and the ten integer types.
(defun cast-checks-to-ints (from fw fs ts)
  (if (atom ts)
      t
    (and (cast-check from fw fs 4 (first (car ts)) (second (car ts)))
         (cast-checks-to-ints from fw fs (cdr ts)))))

(defun cast-checks-to-non-ints (from fw fs ds)
  (if (atom ds)
      t
    (and (cast-check from fw fs (car ds) 8 nil)
         (cast-checks-to-non-ints from fw fs (cdr ds)))))

(defun cast-checks-all (from fw fs)
  (and (cast-checks-to-non-ints from fw fs *non-int-dests*)
       (cast-checks-to-ints from fw fs *int-types*)))

(defun int-cast-checks (srcs)
  (if (atom srcs)
      t
    (and (cast-checks-all 4 (first (car srcs)) (second (car srcs)))
         (int-cast-checks (cdr srcs)))))

(defcheck boolean-cast-extraction
  (cast-checks-all 1 0 nil))

; cast_lossy is the cast for every destination but IdentifierLiteral, which
; has no CastLossy impl.
(defun boolean-cast-lossy-checks (ds)
  (if (atom ds)
      t
    (and (same-circuit (ext-run (acl2::circuits-h-p-cast *fuel* 1 0 nil (car ds) 8 nil))
                       (progx-boolean-cast-lossy-gadget)
                       nil)
         (boolean-cast-lossy-checks (cdr ds)))))

(defcheck boolean-cast-lossy-extraction
  (and (boolean-cast-lossy-checks '(0 1 2 3 4 5))
       (same-circuit (ext-run (acl2::circuits-h-p-cast *fuel* 1 0 nil 4 128 t))
                     (progx-boolean-cast-lossy-gadget)
                     nil)))

(defcheck field-cast-extraction
  (cast-checks-all 2 0 nil))

(defcheck integer-cast-extraction
  (int-cast-checks *int-types*))

(defcheck scalar-cast-extraction
  (cast-checks-all 5 0 nil))

(defcheck identifier-literal-cast-extraction
  (cast-checks-all 6 0 nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Equalities

(defun equal-check (op gadget inputs)
  (same-circuit-renamed (ext-run (acl2::circuits-h-p-equal *fuel* op)) gadget inputs nil))

(defcheck identifier-is-equal-extraction
  (equal-check 0 (identifier-is-equal-gadget (wv 1) (wv 2) 'm 'r (base-prime))
               (wvs 1 2)))

(defcheck identifier-is-not-equal-extraction
  (equal-check 1 (identifier-is-not-equal-gadget (wv 1) (wv 2) 'm 'r (base-prime))
               (wvs 1 2)))

(defcheck program-id-is-equal-extraction
  (equal-check 2 (program-id-is-equal-gadget (wv 1) (wv 3) 'mn 'rn (wv 2) (wv 4) 'mw 'rw 'z
                                             (base-prime))
               (wvs 1 4)))

(defcheck program-id-is-not-equal-extraction
  (equal-check 3 (program-id-is-not-equal-gadget (wv 1) (wv 3) 'mn 'rn (wv 2) (wv 4) 'mw 'rw 'z
                                                 (base-prime))
               (wvs 1 4)))

; snarkVM evaluates ((a & b) & c) & d left to right, so each AND follows
; the equality it consumes; the gadget lists the four equalities first.
; Wires: results and multipliers W9..W12, the first AND W13, W14 W15, the
; second AND W16, W17 W18, the last AND W19.
(defun dynamic-future-explicit (neq)
  (if neq
      (dynamic-future-is-not-equal-gadget
       (wv 1) (wv 5) (wv 10) (wv 9) (wv 2) (wv 6) (wv 12) (wv 11)
       (wv 3) (wv 7) (wv 15) (wv 14) (wv 4) (wv 8) (wv 18) (wv 17)
       (wv 13) (wv 16) (wv 19) (base-prime))
    (dynamic-future-is-equal-gadget
     (wv 1) (wv 5) (wv 10) (wv 9) (wv 2) (wv 6) (wv 12) (wv 11)
     (wv 3) (wv 7) (wv 15) (wv 14) (wv 4) (wv 8) (wv 18) (wv 17)
     (wv 13) (wv 16) (wv 19) (base-prime))))

(defcheck dynamic-future-is-equal-extraction
  (same-circuit-unordered (ext-run (acl2::circuits-h-p-equal *fuel* 4))
                          (dynamic-future-explicit nil) nil))

(defcheck dynamic-future-is-not-equal-extraction
  (same-circuit-unordered (ext-run (acl2::circuits-h-p-equal *fuel* 5))
                          (dynamic-future-explicit t) nil))

; The version's field value is the bits' linear combination.
(defcheck record-is-hiding-extraction
  (same-circuit-renamed (ext-run (acl2::circuits-h-p-record-is-hiding *fuel*))
                        (crypto-record-is-hiding-gadget 'v 'm 'r (base-prime))
                        (wvs 1 8)
                        (list (cons 'v (lebits-lc (wvs 1 8) 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; OutputID: expected hash W1, output hash W2.

(defun output-id-check (gadget)
  (same-circuit (ext-run (acl2::circuits-h-p-output-id *fuel*)) gadget nil))

(defcheck output-id-public-extraction
  (output-id-check (crypto-make-output-id-public-gadget (wv 2) (wv 1))))

(defcheck output-id-private-extraction
  (output-id-check (crypto-make-output-id-private-gadget (wv 2) (wv 1))))

(defcheck output-id-external-record-extraction
  (output-id-check (crypto-make-output-id-external-record-gadget (wv 2) (wv 1))))

; OutputID::record: expected W1..W3, injected W4..W6, the two is_not_equal
; pairs (r, m) W7, W8 and W9, W10, and the OR W11.
(defcheck output-id-record-extraction
  (same-circuit (ext-run (acl2::circuits-h-p-output-id-record *fuel*))
                (crypto-make-output-id-record-gadget (wv 4) (wv 1) (wv 5) (wv 2) (wv 6) (wv 3)
                                                     (wv 8) (wv 7) (wv 10) (wv 9) (wv 11)
                                                     (base-prime))
                nil))

(defcheck output-id-future-extraction
  (output-id-check (crypto-make-output-id-future-gadget (wv 2) (wv 1))))

(defcheck output-id-dynamic-record-extraction
  (output-id-check (crypto-make-output-id-dynamic-record-gadget (wv 2) (wv 1))))

(defcheck output-id-dynamic-future-extraction
  (output-id-check (crypto-make-output-id-dynamic-future-gadget (wv 2) (wv 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Literal::new. Every wire is internal: the injected wires are renamed too.

(defun group-new-g (prefix)
  (b* ((g (gs prefix 14)))
    (literal-group-new-gadget (nth 0 g) (nth 1 g) (nth 2 g) (nth 3 g) (nth 4 g)
                              (nth 5 g) (nth 6 g) (nth 7 g) (nth 8 g) (nth 9 g)
                              (nth 10 g) (nth 11 g) (nth 12 g) (nth 13 g)
                              (base-prime))))

; Without the compute key's hash_to_scalar, which neither side models.
(defun signature-new-g ()
  (b* ((k (gs "PK" 14)) (q (gs "PR" 14)))
    (literal-signature-new-gadget
     'c (gs "CX" 251) (gs "CR" 250) 'r (gs "RX" 251) (gs "RR" 250)
     (nth 0 k) (nth 1 k) (nth 2 k) (nth 3 k) (nth 4 k) (nth 5 k) (nth 6 k)
     (nth 7 k) (nth 8 k) (nth 9 k) (nth 10 k) (nth 11 k) (nth 12 k) (nth 13 k)
     (nth 0 q) (nth 1 q) (nth 2 q) (nth 3 q) (nth 4 q) (nth 5 q) (nth 6 q)
     (nth 7 q) (nth 8 q) (nth 9 q) (nth 10 q) (nth 11 q) (nth 12 q) (nth 13 q)
     (base-prime))))

(defun literal-new-check (variant n s gadget)
  (same-circuit-renamed (ext-run (acl2::circuits-h-p-literal-new *fuel* variant n s))
                        gadget nil nil))

(defun literal-new-int-checks (ts)
  (if (atom ts)
      t
    (and (literal-new-check 4 (first (car ts)) (second (car ts))
                            (literal-integer-new-gadget (gs "B" (first (car ts)))
                                                        (base-prime)))
         (literal-new-int-checks (cdr ts)))))

(defcheck literal-new-extraction
  (and (literal-new-check 0 0 nil (group-new-g "A"))
       (literal-new-check 1 0 nil (literal-boolean-new-gadget 'b (base-prime)))
       (literal-new-check 2 0 nil (literal-field-new-gadget))
       (literal-new-check 3 0 nil (group-new-g "G"))
       (literal-new-int-checks *int-types*)
       (literal-new-check 5 0 nil (literal-scalar-new-gadget 's (gs "X" 251) (gs "R" 250)
                                                            (base-prime)))
       (literal-new-check 6 0 nil (signature-new-g))
       (literal-new-check 7 0 nil
                          (literal-identifier-new-gadget (sym-rows "BR" 0 31 8)
                                                         (sym-rows "WR" 0 31 12)
                                                         'partial 'uscore 'islet
                                                         (base-prime)))))
