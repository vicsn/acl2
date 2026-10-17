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

(defun int-check-name (name n)
  (declare (xargs :mode :program))
  (acl2::packn-pos (list 'int- name '- n '-extraction) 'xs))

(defmacro int-check (name n form)
  `(defcheck ,(int-check-name name n) ,form))

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
