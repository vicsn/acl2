; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Extraction checks for circuit/types/integers, variable operands, at every
; width 8, 16, 32, 64, and 128.

(include-book "check-lib")
(include-book "../fun-circuits/int-bitwise")
(include-book "../fun-circuits/int-ternary")
(include-book "../fun-circuits/int-equal")
(include-book "../fun-circuits/int-add")
(include-book "../fun-circuits/int-sub")
(include-book "../fun-circuits/int-abs")
(include-book "../fun-circuits/int-neg")
(include-book "../fun-circuits/int-compare")
(include-book "../fun-circuits/int-bits")
(include-book "../fun-circuits/int-field")
(include-book "../fun-circuits/int-new")
(include-book "../fun-circuits/int-mul")
(include-book "../fun-circuits/int-mulpow-checked")
(include-book "../fun-circuits/int-mulpow-karatsuba")
(include-book "../fun-circuits/int-mulpow-signed-checked")
(include-book "../fun-circuits/int-div")
(include-book "../fun-circuits/int-divshift-unsigned-div")
(include-book "../fun-circuits/int-divshift-signed-div")
(include-book "../fun-circuits/int-divshift-signed-div-checked")
(include-book "../fun-circuits/int-divshift-signed-div-128")
(include-book "../fun-circuits/int-divshift-signed-div-checked-128")
(include-book "../fun-circuits/int-shift-pfcs")
(include-book "../fun-circuits/int-divshift-shl-checked-signed")
(include-book "../fun-circuits/int-divshift-shr-signed")
(include-book "../fun-circuits/int-divshift-shr-checked-signed")
(include-book "../fun-circuits/int-divshift-shl-wrapped-128")
(include-book "../fun-circuits/int-divshift-shr-unsigned-128")
(include-book "../fun-circuits/int-divshift-shr-signed-128")
(include-book "../fun-circuits/int-divshift-shr-checked-unsigned-128")
(include-book "../fun-circuits/int-divshift-shr-checked-signed-128")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Binary operations: x is W1..Wn, y is W(n+1)..W(2n), and the operation's
; own wires start at W(2n+1). Unary operations: x is W1..Wn and the
; operation's wires start at W(n+1). The gadget symbol ONE is the constant 1;
; the symbols K0 and K1 are constant bits 0 and 1.

(defconst *one* '((one . 1)))
(defconst *k* '((one . 1) (k0 . 0) (k1 . 1)))

(defun xs (n) (wvs 1 n))
(defun ys (n) (wvs (+ n 1) n))
(defun zs (n) (wvs (+ (* 2 n) 1) n))
(defun aux (n k) (wv (+ (* 3 n) k)))
(defun k0s (n) (repeat n 'k0))
(defun k1s (n) (cons 'k1 (repeat (1- n) 'k0)))

(defconst *r* (bits-lt-prime-rlen (base-prime)))

; mul_and_check from wire LO: the witnessed product for 2n < 252, otherwise
; Karatsuba's z0, z2, m, then the n product bits and n/2 + 1 carry bits.
; The list is z0 z2 m zs carry next, where next is the first free wire.

(defun mul-wires (n lo)
  (if (< (* 2 n) 252)
      (list 'z0 'z2 'm (wvs lo n) nil (+ lo n))
    (list (wv lo) (wv (+ lo 1)) (wv (+ lo 2))
          (wvs (+ lo 3) n) (wvs (+ lo 3 n) (1+ (floor n 2)))
          (+ lo 3 n (1+ (floor n 2))))))

(defun mul-checked-unsigned-gadget (n)
  (b* (((list z0 z2 m zs carry &) (mul-wires n (+ (* 2 n) 1))))
    (int-mul-checked-unsigned-any-gadget (xs n) (ys n) z0 z2 m zs carry (base-prime))))

; Signed mul_checked: |x| is W(3n+2)..; |y| W(5n+3)..; the product follows,
; then xor, the positive-overflow and, the or-fold of the low n-1 product
; bits, the underflow terms, 0 - product, and the result.

(defun mul-checked-signed-gadget (n)
  (b* (((list z0 z2 m ps carry b) (mul-wires n (+ (* 6 n) 3))))
    (int-mul-checked-signed-gadget
     (xs n) (ys n)
     (wvs (+ (* 3 n) 2) n) (wvs (+ (* 2 n) 1) n) (wv (+ (* 3 n) 1))
     (wvs (+ (* 5 n) 3) n) (wvs (+ (* 4 n) 2) n) (wv (+ (* 5 n) 2))
     z0 z2 m ps carry
     (wv b) (wvs (+ b 2) (- n 2)) (wv (+ b 1)) (wv (+ b n)) (wv (+ b n 1))
     (wv (+ b n 2)) (wvs (+ b n 3) n) (wv (+ b (* 2 n) 3)) (wvs (+ b (* 2 n) 4) n)
     'one (base-prime))))

; Division. The gadgets are called on fresh internal symbols, and the checks
; are up to a renaming of internal wires (same-circuit-renamed).

(defun unsigned-div-gadget (xs ys n)
  (if (< (* 2 n) 252)
      (int-unsigned-division-via-witness-gadget xs ys (gs "Q" n) (gs "R" n) 'm (gs "D" n)
                                                'd 'one (base-prime))
    (unsigned-medium-div-gadget xs ys (gs "Q" n) (gs "R" n) 'll 'hl 'lh 'hh (gs "MS" n)
                                (gs "MCL" (1+ (floor n 2))) (gs "MCH" n) (gs "LS" n) 'l
                                (gs "D" n) 'd 'one (base-prime))))

(defun signed-div-gadget (n rem)
  (b* ((xs (xs n)) (ys (ys n)) (p (base-prime)))
    (if (< (* 2 n) 252)
        (if rem
            (int-divshift-signed-rem-wrapped-gadget
             xs ys (gs "AX" n) (gs "MX" n) 'cx (gs "AY" n) (gs "MY" n) 'cy
             (gs "Q" n) (gs "R" n) 'm (gs "D" n) 'd (gs "N" n) 'nc (gs "Z" n) 'one p)
          (int-divshift-signed-div-wrapped-gadget
           xs ys (gs "AX" n) (gs "MX" n) 'cx (gs "AY" n) (gs "MY" n) 'cy
           (gs "Q" n) (gs "R" n) 'm (gs "D" n) 'd 's (gs "N" n) 'nc (gs "Z" n) 'one p))
      (if rem
          (int-divshift-signed-rem-wrapped-128-gadget
           xs ys (gs "AX" n) (gs "MX" n) 'cx (gs "AY" n) (gs "MY" n) 'cy
           (gs "Q" n) (gs "R" n) 'll 'hl 'lh 'hh (gs "MS" n) (gs "MCL" (1+ (floor n 2)))
           (gs "MCH" n) (gs "LS" n) 'l (gs "D" n) 'd (gs "N" n) 'nc (gs "Z" n) 'one p)
        (int-divshift-signed-div-wrapped-128-gadget
         xs ys (gs "AX" n) (gs "MX" n) 'cx (gs "AY" n) (gs "MY" n) 'cy
         (gs "Q" n) (gs "R" n) 'll 'hl 'lh 'hh (gs "MS" n) (gs "MCL" (1+ (floor n 2)))
         (gs "MCH" n) (gs "LS" n) 'l (gs "D" n) 'd 's (gs "N" n) 'nc (gs "Z" n) 'one p)))))

; The checked gadgets add int-divshift-overflow-check-gadget, whose two
; int-is-equal-gadget calls each start with the Boolean check that snarkVM
; does not emit (see the equality checks). SNARKVM-OVERFLOW-CHECK is the
; overflow check without those two constraints.

(defun min-bits (n) (append (repeat (1- n) 'k0) (list 'k1)))
(defun neg-one-bits (n) (repeat n 'k1))

(defun overflow-check-parts (n)
  (b* ((p (base-prime)))
    (list (int-is-equal-gadget (xs n) (min-bits n) 'e1 'mul1 'one p)
          (int-is-equal-gadget (ys n) (neg-one-bits n) 'e2 'mul2 'one p)
          (append (boolean-nor-gadget 'e1 'e2 'ov p)
                  (int-divshift-assert-not-gadget 'ov p)))))

(defun snarkvm-overflow-check (n)
  (b* (((list eq1 eq2 rest) (overflow-check-parts n)))
    (append (cdr eq1) (cdr eq2) rest)))

(defun overflow-check-differs (n)
  (b* (((list eq1 eq2 rest) (overflow-check-parts n)))
    (and (equal (int-divshift-overflow-check-gadget (xs n) (ys n) (min-bits n)
                                                    (neg-one-bits n) 'e1 'mul1 'e2 'mul2 'ov
                                                    'one (base-prime))
                (append eq1 eq2 rest))
         (equal (car eq1) (car (boolean-check-gadget 'e1 (base-prime))))
         (equal (car eq2) (car (boolean-check-gadget 'e2 (base-prime)))))))

(defun int-check-name (name n)
  (declare (xargs :mode :program))
  (acl2::packn-pos (list 'int- name '- n '-extraction) 'xs))

(defmacro int-check (name n form)
  `(defcheck ,(int-check-name name n) ,form))

(defmacro int-division-checks (n)
  `(progn
     ; Unsigned div and rem, wrapped and checked, are the quotient and the
     ; remainder of one circuit; so is modulo.
     (int-check unsigned-division ,n
       (b* ((ext (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 16))))
         (and (same-circuit-renamed ext (unsigned-div-gadget (xs ,n) (ys ,n) ,n)
                                    (wvs 1 (* 2 ,n)) *one*)
              (equal (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 17)) ext)
              (equal (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 18)) ext)
              (equal (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 19)) ext)
              (equal (ext-run (acl2::circuits-h-i-modulo *fuel* ,n)) ext))))

     (int-check div-wrapped-signed ,n
       (same-circuit-renamed (ext-run (acl2::circuits-h-i-binop *fuel* ,n t 16))
                             (signed-div-gadget ,n nil) (wvs 1 (* 2 ,n)) *one*))

     (int-check rem-wrapped-signed ,n
       (same-circuit-renamed (ext-run (acl2::circuits-h-i-binop *fuel* ,n t 18))
                             (signed-div-gadget ,n t) (wvs 1 (* 2 ,n)) *one*))

     (int-check div-checked-signed ,n
       (and (overflow-check-differs ,n)
            (same-circuit-renamed (ext-run (acl2::circuits-h-i-binop *fuel* ,n t 17))
                                  (append (snarkvm-overflow-check ,n) (signed-div-gadget ,n nil))
                                  (wvs 1 (* 2 ,n)) *k*)))

     (int-check rem-checked-signed ,n
       (and (overflow-check-differs ,n)
            (same-circuit-renamed (ext-run (acl2::circuits-h-i-binop *fuel* ,n t 19))
                                  (append (snarkvm-overflow-check ,n) (signed-div-gadget ,n t))
                                  (wvs 1 (* 2 ,n)) *k*)))))

(defmacro int-checks (n)
  `(progn

     (int-check bitand ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 0))
                     (int-bitand-gadget (xs ,n) (ys ,n) (zs ,n))
                     nil))

     (int-check bitor ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 1))
                     (int-bitor-gadget (xs ,n) (ys ,n) (zs ,n) (base-prime))
                     nil))

     (int-check bitxor ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 2))
                     (int-bitxor-gadget (xs ,n) (ys ,n) (zs ,n) (base-prime))
                     nil))

     ; The gadget's first constraint is a Boolean check of the result that
     ; snarkVM does not emit; snarkVM's circuit is the other two.
     (int-check is-equal ,n
       (let ((ext (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 3)))
             (gad (int-is-equal-gadget (xs ,n) (ys ,n) (wv (+ (* 2 ,n) 1))
                                       (wv (+ (* 2 ,n) 2)) 'one (base-prime))))
         (and (equal (len gad) 3)
              (same-circuit ext (cdr gad) *one*)
              (not (same-circuit ext gad *one*)))))

     (int-check is-not-equal ,n
       (let ((ext (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 4)))
             (gad (int-is-not-equal-gadget (xs ,n) (ys ,n) (wv (+ (* 2 ,n) 1))
                                           (wv (+ (* 2 ,n) 2)) 'one (base-prime))))
         (and (equal (len gad) 3)
              (same-circuit ext (cdr gad) *one*)
              (not (same-circuit ext gad *one*)))))

     (int-check is-zero ,n
       (let ((ext (ext-run (acl2::circuits-h-i-unop *fuel* ,n nil 1)))
             (gad (int-is-zero-gadget (xs ,n) (k0s ,n) (wv (+ ,n 1))
                                      (wv (+ ,n 2)) 'one (base-prime))))
         (and (equal (len gad) 3)
              (same-circuit ext (cdr gad) *k*)
              (not (same-circuit ext gad *k*)))))

     (int-check is-one ,n
       (let ((ext (ext-run (acl2::circuits-h-i-unop *fuel* ,n nil 2)))
             (gad (int-is-one-gadget (xs ,n) (k1s ,n) (wv (+ ,n 1))
                                     (wv (+ ,n 2)) 'one (base-prime))))
         (and (equal (len gad) 3)
              (same-circuit ext (cdr gad) *k*)
              (not (same-circuit ext gad *k*)))))

     ; snarkVM witnesses the sum and has no carry wire. The gadget is
     ; snarkVM's circuit once its carry is fixed at 0.
     (int-check add-checked-unsigned ,n
       (let ((ext (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 5)))
             (gad (int-add-checked-unsigned-gadget (xs ,n) (ys ,n) (zs ,n)
                                                   'carry (base-prime))))
         (and (same-circuit ext gad '((carry . 0)))
              (not (same-circuit ext gad nil)))))

     (int-check add-checked-signed ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n t 5))
                     (int-add-checked-signed-gadget (xs ,n) (ys ,n) (zs ,n) (aux ,n 1)
                                                    (aux ,n 2) (aux ,n 3) (aux ,n 4)
                                                    'one (base-prime))
                     *one*))

     (int-check add-wrapped-unsigned ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 6))
                     (int-add-wrapped-unsigned-gadget (xs ,n) (ys ,n) (zs ,n) (aux ,n 1)
                                                      (base-prime))
                     nil))

     (int-check add-wrapped-signed ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n t 6))
                     (int-add-wrapped-signed-gadget (xs ,n) (ys ,n) (zs ,n) (aux ,n 1)
                                                    (base-prime))
                     nil))

     (int-check sub-checked-unsigned ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 7))
                     (int-sub-checked-unsigned-gadget (xs ,n) (ys ,n) (zs ,n) (aux ,n 1)
                                                      'one (base-prime))
                     *one*))

     (int-check sub-checked-signed ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n t 7))
                     (int-sub-checked-signed-gadget (xs ,n) (ys ,n) (zs ,n) (aux ,n 1)
                                                    (aux ,n 2) (aux ,n 3) (aux ,n 4)
                                                    'one (base-prime))
                     *one*))

     (int-check sub-wrapped-unsigned ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 8))
                     (int-sub-wrapped-unsigned-gadget (xs ,n) (ys ,n) (zs ,n) (aux ,n 1)
                                                      'one (base-prime))
                     *one*))

     (int-check sub-wrapped-signed ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n t 8))
                     (signed-small-sub-wrapped-gadget (xs ,n) (ys ,n) (zs ,n) (aux ,n 1)
                                                      'one (base-prime))
                     *one*))

     (int-check is-less-than-unsigned ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 9))
                     (int-is-less-than-unsigned-gadget (xs ,n) (ys ,n) (zs ,n) (aux ,n 1)
                                                       (base-prime))
                     nil))

     (int-check is-greater-than-unsigned ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 10))
                     (int-is-greater-than-unsigned-gadget (xs ,n) (ys ,n) (zs ,n) (aux ,n 1)
                                                          (base-prime))
                     nil))

     (int-check is-less-than-or-equal-unsigned ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 11))
                     (int-is-less-than-or-equal-unsigned-gadget (xs ,n) (ys ,n) (zs ,n)
                                                                (aux ,n 1) (base-prime))
                     nil))

     (int-check is-greater-than-or-equal-unsigned ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 12))
                     (int-is-greater-than-or-equal-unsigned-gadget (xs ,n) (ys ,n) (zs ,n)
                                                                   (aux ,n 1) (base-prime))
                     nil))

     ; Signed comparisons: snarkVM emits the sign constraints before the
     ; unsigned comparison, the gadget after, so the order is ignored.
     ; diff is W(2n+1), negpos W(2n+2), the comparison bits W(2n+3)..,
     ; z W(3n+3), and the result W(3n+4).
     (int-check is-less-than-signed ,n
       (same-circuit-unordered
        (ext-run (acl2::circuits-h-i-binop *fuel* ,n t 9))
        (int-is-less-than-signed-gadget (xs ,n) (ys ,n) (wvs (+ (* 2 ,n) 3) ,n)
                                        (aux ,n 3) (wv (+ (* 2 ,n) 1)) (wv (+ (* 2 ,n) 2))
                                        (aux ,n 4) 'one (base-prime))
        *one*))

     (int-check is-greater-than-signed ,n
       (same-circuit-unordered
        (ext-run (acl2::circuits-h-i-binop *fuel* ,n t 10))
        (int-is-greater-than-signed-gadget (xs ,n) (ys ,n) (wvs (+ (* 2 ,n) 3) ,n)
                                           (aux ,n 3) (wv (+ (* 2 ,n) 1)) (wv (+ (* 2 ,n) 2))
                                           (aux ,n 4) 'one (base-prime))
        *one*))

     (int-check is-less-than-or-equal-signed ,n
       (same-circuit-unordered
        (ext-run (acl2::circuits-h-i-binop *fuel* ,n t 11))
        (int-is-less-than-or-equal-signed-gadget (xs ,n) (ys ,n) (wvs (+ (* 2 ,n) 3) ,n)
                                                 (aux ,n 3) (wv (+ (* 2 ,n) 1))
                                                 (wv (+ (* 2 ,n) 2)) (aux ,n 4)
                                                 'one (base-prime))
        *one*))

     (int-check is-greater-than-or-equal-signed ,n
       (same-circuit-unordered
        (ext-run (acl2::circuits-h-i-binop *fuel* ,n t 12))
        (int-is-greater-than-or-equal-signed-gadget (xs ,n) (ys ,n) (wvs (+ (* 2 ,n) 3) ,n)
                                                    (aux ,n 3) (wv (+ (* 2 ,n) 1))
                                                    (wv (+ (* 2 ,n) 2)) (aux ,n 4)
                                                    'one (base-prime))
        *one*))

     ; abs: 0 - x is W(n+1)..W(2n) with carry W(2n+1); checked adds the
     ; underflow wires W(2n+2) and W(2n+3); the ternary result follows.
     (int-check abs-checked-signed ,n
       (same-circuit (ext-run (acl2::circuits-h-i-unop *fuel* ,n t 3))
                     (int-abs-checked-signed-gadget (xs ,n) (wvs (+ (* 2 ,n) 4) ,n)
                                                    (wvs (+ ,n 1) ,n) (wv (+ (* 2 ,n) 1))
                                                    (wv (+ (* 2 ,n) 2)) (wv (+ (* 2 ,n) 3))
                                                    'one (base-prime))
                     *one*))

     (int-check abs-wrapped-signed ,n
       (same-circuit (ext-run (acl2::circuits-h-i-unop *fuel* ,n t 4))
                     (int-abs-wrapped-signed-gadget (xs ,n) (wvs (+ (* 2 ,n) 2) ,n)
                                                    (wvs (+ ,n 1) ,n) (wv (+ (* 2 ,n) 1))
                                                    'one (base-prime))
                     *one*))

     (int-check abs-checked-unsigned ,n
       (same-circuit (ext-run (acl2::circuits-h-i-unop *fuel* ,n nil 3))
                     (int-abs-checked-unsigned-gadget)
                     nil))

     (int-check abs-wrapped-unsigned ,n
       (same-circuit (ext-run (acl2::circuits-h-i-unop *fuel* ,n nil 4))
                     (int-abs-wrapped-unsigned-gadget)
                     nil))

     (int-check neg-signed ,n
       (same-circuit (ext-run (acl2::circuits-h-i-unop *fuel* ,n t 5))
                     (int-neg-signed-gadget (xs ,n) (wvs (+ ,n 1) ,n) (wv (+ (* 2 ,n) 1))
                                            (wv (+ (* 2 ,n) 2)) 'one (base-prime))
                     *one*))

     (int-check mul-wrapped ,n
       (and (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 13))
                          (int-mul-wrapped-gadget (xs ,n) (ys ,n) (wv (+ (* 2 ,n) 1))
                                                  (wv (+ (* 2 ,n) 2)) (wv (+ (* 2 ,n) 3))
                                                  (wvs (+ (* 2 ,n) 4) ,n)
                                                  (wvs (+ (* 3 ,n) 4) (1+ (floor ,n 2)))
                                                  (base-prime))
                          nil)
            (equal (ext-run (acl2::circuits-h-i-binop *fuel* ,n t 13))
                   (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 13)))))

     (int-check mul-checked-unsigned ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 14))
                     (mul-checked-unsigned-gadget ,n)
                     nil))

     (int-check mul-checked-signed ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n t 14))
                     (mul-checked-signed-gadget ,n)
                     *one*))

     (int-check karatsuba-multiply ,n
       (same-circuit (ext-run (acl2::circuits-h-i-binop *fuel* ,n nil 15))
                     (int-karatsuba-multiply-gadget (xs ,n) (ys ,n) (wv (+ (* 2 ,n) 1))
                                                    (wv (+ (* 2 ,n) 2)) (wv (+ (* 2 ,n) 3))
                                                    (wvs (+ (* 2 ,n) 4) (+ ,n (floor ,n 2) 1))
                                                    (base-prime))
                     nil))

     (int-check ternary ,n
       (same-circuit (ext-run (acl2::circuits-h-i-ternary *fuel* ,n nil))
                     (int-ternary-gadget (wv 1) (wvs 2 ,n) (wvs (+ ,n 2) ,n)
                                         (wvs (+ (* 2 ,n) 2) ,n) (base-prime))
                     nil))

     (int-check new ,n
       (same-circuit (ext-run (acl2::circuits-h-i-unop *fuel* ,n nil 0))
                     (int-new-gadget (xs ,n) (base-prime))
                     nil))

     (int-check to-field ,n
       (same-circuit (ext-run (acl2::circuits-h-i-unop *fuel* ,n nil 6))
                     (int-to-field-gadget)
                     nil))

     (int-check to-fields ,n
       (same-circuit (ext-run (acl2::circuits-h-i-unop *fuel* ,n nil 6))
                     (int-to-fields-gadget)
                     nil))

     (int-check to-scalar ,n
       (same-circuit (ext-run (acl2::circuits-h-i-unop *fuel* ,n nil 8))
                     (int-to-scalar-gadget)
                     nil))

     ; from_bits with n + 4 input bits: the 4 excess bits are asserted zero.
     (int-check from-bits-le ,n
       (and (same-circuit (ext-run (acl2::circuits-h-i-from-bits *fuel* (+ ,n 4) ,n nil nil))
                          (int-from-bits-le-gadget (wvs (+ ,n 1) 4))
                          nil)
            (same-circuit (ext-run (acl2::circuits-h-i-from-bits *fuel* ,n ,n nil nil))
                          (int-from-bits-le-gadget nil)
                          nil)))

     (int-check from-bits-be ,n
       (and (same-circuit (ext-run (acl2::circuits-h-i-from-bits *fuel* (+ ,n 4) ,n nil t))
                          (int-from-bits-be-gadget (reverse (wvs 1 4)))
                          nil)
            (same-circuit (ext-run (acl2::circuits-h-i-from-bits *fuel* ,n ,n nil t))
                          (int-from-bits-be-gadget nil)
                          nil)))

     (int-check from-field ,n
       (same-circuit (ext-run (acl2::circuits-h-i-from-field *fuel* ,n nil nil))
                     (int-from-field-gadget (wv 1) (wvs 2 ,n) (base-prime))
                     nil))

     (int-check from-field-lossy ,n
       (same-circuit (ext-run (acl2::circuits-h-i-from-field *fuel* ,n nil t))
                     (int-from-field-lossy-gadget (wv 1) (wvs 2 253) (wvs 255 *r*)
                                                  'one (base-prime))
                     *one*))))

(int-checks 8)
(int-checks 16)
(int-checks 32)
(int-checks 64)
(int-checks 128)

(int-division-checks 8)
(int-division-checks 16)
(int-division-checks 32)
(int-division-checks 64)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 128-bit division. unsigned-medium-div-gadget, which the 128-bit division
; proofs use, multiplies through unsigned-medium-mul-checked-gadget: four
; partial products and a zero check of each of 128 high carry bits.
; snarkVM's 128-bit mul_checked is Karatsuba with one assert_bits_are_zero
; and z2 = 0 (int-mul-and-check-large-gadget), so the gadgets do not match.
; snarkVM's circuit is the same composition with the Karatsuba mul_checked.

(defun unsigned-div-128-snarkvm-gadget ()
  (b* ((n 128) (p (base-prime)) (q (gs "Q" n)) (r (gs "R" n)) (ms (gs "MS" n)))
    (append (boolean-check-gadget-list q p)
            (boolean-check-gadget-list r p)
            (int-mul-checked-unsigned-any-gadget q (ys n) 'z0 'z2 'm ms
                                                 (gs "MC" (1+ (floor n 2))) p)
            (int-add-checked-unsigned-gadget ms r (gs "LS" n) 'carry p)
            (list (r1cs::make-r1cs-constraint :a (pow2sum-vector (xs n) 0)
                                              :b (list (list 1 1))
                                              :c (pow2sum-vector (gs "LS" n) 0)))
            (unsigned-small-lt-gadget r (ys n) (gs "D" n) 'd p)
            (zero-unit-gadget 'd 'one p))))

(defcheck int-unsigned-division-128-extraction
  (b* ((ext (ext-run (acl2::circuits-h-i-binop *fuel* 128 nil 16))))
    (and (same-circuit-renamed ext (unsigned-div-128-snarkvm-gadget) (wvs 1 256)
                               '((one . 1) (carry . 0)))
         (equal (ext-run (acl2::circuits-h-i-binop *fuel* 128 nil 17)) ext)
         (equal (ext-run (acl2::circuits-h-i-binop *fuel* 128 nil 18)) ext)
         (equal (ext-run (acl2::circuits-h-i-binop *fuel* 128 nil 19)) ext)
         (equal (ext-run (acl2::circuits-h-i-modulo *fuel* 128)) ext))))

(defcheck int-unsigned-division-128-differs
  (b* ((ext (ext-run (acl2::circuits-h-i-binop *fuel* 128 nil 16)))
       (gad (unsigned-div-gadget (xs 128) (ys 128) 128)))
    (and (equal (len (canon-constraints ext nil (base-prime))) 716)
         (equal (len (canon-constraints gad *one* (base-prime))) 1039))))

(defun signed-division-128-differs (op rem checked)
  (b* ((ext (ext-run (acl2::circuits-h-i-binop *fuel* 128 t op)))
       (gad (if checked
                (append (snarkvm-overflow-check 128) (signed-div-gadget 128 rem))
              (signed-div-gadget 128 rem))))
    (not (equal (len (canon-constraints ext nil (base-prime)))
                (len (canon-constraints gad *k* (base-prime)))))))

(defcheck int-signed-division-128-differs
  (and (signed-division-128-differs 16 nil nil)
       (signed-division-128-differs 17 nil t)
       (signed-division-128-differs 18 t nil)
       (signed-division-128-differs 19 t t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Shifts of x (W1..Wn) by an m-bit magnitude e (W(n+1)..W(n+m)), for each
; magnitude width 8, 16, 32. The low k = log2(n) bits of e drive the select
; chain; the others are the excess bits that the checked forms assert zero.

(defun log2-width (n) (if (<= n 8) 3 (if (<= n 16) 4 (if (<= n 32) 5 (if (<= n 64) 6 7)))))

(defun shift-ext (n signedp m op)
  (ext-run (acl2::circuits-h-i-shift *fuel* n signedp m op)))

(defun shift-gadget (n signedp m op)
  (b* ((p (base-prime))
       (k (log2-width n))
       (xs (xs n))
       (ebits (wvs (+ n 1) k))
       (excess (wvs (+ n 1 k) (- m k)))
       (nexts (gs "NX" k)))
    (case op
      (0 (int-shl-wrapped-gadget xs ebits nexts (gs "Z" (* 2 n)) p))
      (1 (if signedp
             (int-divshift-shl-checked-signed-gadget xs ebits excess nexts (gs "Z" (* 3 n)) p)
           (int-shl-checked-shift-gadget xs ebits excess nexts (gs "Z" (* 2 n))
                                         (nthcdr n (gs "Z" (* 2 n))) p)))
      (2 (if signedp
             (int-divshift-shr-signed-gadget xs ebits nexts (gs "Z" (* 2 n)) p)
           (int-shr-wrapped-gadget xs ebits nexts (gs "Z" (* 2 n)) p)))
      (t (if signedp
             (int-divshift-shr-checked-signed-gadget xs ebits excess nexts (gs "Z" (* 2 n)) p)
           (int-shr-checked-shift-gadget xs ebits excess nexts (gs "Z" (* 2 n)) p))))))

(defun shift-check (n signedp m op)
  (same-circuit-renamed (shift-ext n signedp m op) (shift-gadget n signedp m op)
                        (wvs 1 (+ n m)) *one*))

(defun shift-checks-m (n signedp ms op)
  (or (atom ms)
      (and (shift-check n signedp (car ms) op)
           (shift-checks-m n signedp (cdr ms) op))))

(defun shift-checks (ns signedp ms op)
  (or (atom ns)
      (and (shift-checks-m (car ns) signedp ms op)
           (shift-checks (cdr ns) signedp ms op))))

(defconst *small-widths* '(8 16 32 64))
(defconst *magnitudes* '(8 16 32))

(defcheck int-shl-wrapped-extraction
  (and (shift-checks *small-widths* nil *magnitudes* 0)
       (shift-checks *small-widths* t *magnitudes* 0)))

(defcheck int-shl-checked-extraction
  (and (shift-checks *small-widths* nil *magnitudes* 1)
       (shift-checks *small-widths* t *magnitudes* 1)))

(defcheck int-shr-wrapped-extraction
  (and (shift-checks *small-widths* nil *magnitudes* 2)
       (shift-checks *small-widths* t *magnitudes* 2)))

(defcheck int-shr-checked-extraction
  (and (shift-checks *small-widths* nil *magnitudes* 3)
       (shift-checks *small-widths* t *magnitudes* 3)))

; Width 128: 2^e by square-and-select over the 7 low exponent bits, most
; significant first, then to_lower_bits_le(128). shl_wrapped multiplies by it
; with mul_wrapped.

(defun shl-wrapped-128-check (m)
  (same-circuit-renamed
   (shift-ext 128 nil m 0)
   (int-divshift-shl-wrapped-128-gadget (xs 128) (reverse (wvs 129 7)) (gs "SQ" 6) (gs "T" 6)
                                        (gs "Y" 128) 'll 'hl 'lh (gs "Z" 128) (gs "ZH" 65)
                                        (base-prime))
   (wvs 1 (+ 128 m)) nil))

(defcheck int-shl-wrapped-128-extraction
  (and (shl-wrapped-128-check 8)
       (shl-wrapped-128-check 16)
       (shl-wrapped-128-check 32)
       (equal (shift-ext 128 t 8 0) (shift-ext 128 nil 8 0))))

; shr at width 128 divides by 2^e through unsigned-medium-div-gadget, the
; division gadget that does not match snarkVM at 128 bits (see the division
; checks), so these gadgets do not match either.

(defun shr-128-gadget (signedp checked)
  (b* ((p (base-prime)) (n 128) (xs (xs n)) (rb (reverse (wvs 129 7))) (ex (wvs 136 1))
       (sq (gs "SQ" 6)) (ts (gs "T" 6)) (ys (gs "Y" n)) (ax (gs "AX" n)) (mx (gs "MX" n))
       (q (gs "Q" n)) (r (gs "R" n)) (ms (gs "MS" n)) (mcl (gs "MCL" 65)) (mch (gs "MCH" n))
       (ls (gs "LS" n)) (ds (gs "D" n)) (nq (gs "NQ" n)) (zeros (repeat n 'k0))
       (mq (gs "MQ" n)) (rd (gs "RD" n)) (res (gs "RES" n)))
    (cond ((and signedp checked)
           (int-divshift-shr-checked-signed-128-gadget
            ex xs rb sq ts ys ax mx 'cx q r 'll 'hl 'lh 'hh ms mcl mch ls 'l ds 'd
            nq 'nc zeros 'nz 'nw mq 'mc rd res 'one p))
          (signedp
           (int-divshift-shr-signed-128-gadget
            xs rb sq ts ys ax mx 'cx q r 'll 'hl 'lh 'hh ms mcl mch ls 'l ds 'd
            nq 'nc zeros 'nz 'nw mq 'mc rd res 'one p))
          (checked
           (int-divshift-shr-checked-unsigned-128-gadget
            ex xs rb sq ts ys q r 'll 'hl 'lh 'hh ms mcl mch ls 'l ds 'd 'one p))
          (t
           (int-divshift-shr-unsigned-128-gadget
            xs rb sq ts ys q r 'll 'hl 'lh 'hh ms mcl mch ls 'l ds 'd 'one p)))))

(defun shr-128-differs (signedp checked)
  (not (equal (len (canon-constraints (shift-ext 128 signedp 8 (if checked 3 2)) nil (base-prime)))
              (len (canon-constraints (shr-128-gadget signedp checked) *k* (base-prime))))))

(defcheck int-shr-128-differs
  (and (shr-128-differs nil nil)
       (shr-128-differs nil t)
       (shr-128-differs t nil)
       (shr-128-differs t t)))
