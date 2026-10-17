; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Extraction checks for circuit/types/group. A point input is two wires,
; (W1, W2) and then (W3, W4), allocated without constraints.

(include-book "check-lib")
(include-book "../fun-circuits/crv-curve")
(include-book "../fun-circuits/crv-equal")
(include-book "../fun-circuits/crv-ternary")
(include-book "../fun-circuits/crv-bits")
(include-book "../fun-circuits/group-inject-r1cs")
(include-book "../fun-circuits/grp-from-xy-coordinates")
(include-book "../fun-circuits/grp-from-x-coordinate")
(include-book "../fun-circuits/grp-from-bits")
(include-book "../fun-circuits/grp-is-in-group")
(include-book "../fun-circuits/grp-mul")
(include-book "../fun-circuits/scalar-write-bits-r1cs")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *u* '((u . 1)))

(defconst *r* (bits-lt-prime-rlen (base-prime)))

; K lists of N fresh symbols PREFIXi-j.
(defun gsteps (prefix k n)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      nil
    (append (gsteps prefix (1- k) n)
            (list (gs (acl2::packn-pos (list prefix (1- k) "-") 'wv) n)))))

; snarkVM adds with the operands swapped when the second is not constant,
; so for a + b the gadget's first point is b. U is W5, v0 = b.x * a.y is W6,
; v1 = a.x * b.y is W7, v0 * v1 is W8, and the sum is (W9, W10).
(defcheck group-add-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-binop *fuel* 0))
                (crv-group-add-gadget (wv 3) (wv 4) (wv 1) (wv 2)
                                      (wv 5) (wv 6) (wv 7) (wv 8) (wv 9) (wv 10)
                                      (base-prime))
                nil))

; a - b is a + (-b), and -b is the first point of the add. Its v0 is
; (-b.x) * a.y, the gadget's v1, so v0 and v1 trade places and the first
; two products are emitted in the other order.
(defcheck group-sub-extraction
  (same-circuit-unordered (ext-run (acl2::circuits-h-g-binop *fuel* 1))
                          (crv-group-sub-gadget (wv 1) (wv 2) (wv 3) (wv 4)
                                                (wv 5) (wv 7) (wv 6) (wv 8) (wv 9) (wv 10)
                                                (base-prime))
                          nil))

; xy, x^2, y^2 are W3, W4, W5 and the double is (W6, W7).
(defcheck group-double-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-unop *fuel* 0))
                (crv-group-double-gadget (wv 1) (wv 2) (wv 3) (wv 4) (wv 5) (wv 6) (wv 7)
                                         (base-prime))
                nil))

; The double is the input (W3, W4).
(defcheck group-enforce-double-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-binop *fuel* 4))
                (crv-group-enforce-double-gadget (wv 1) (wv 2) (wv 5) (wv 6) (wv 7)
                                                 (wv 3) (wv 4) (base-prime))
                nil))

(defcheck group-mul-by-cofactor-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-unop *fuel* 1))
                (crv-group-mul-by-cofactor-gadget (wv 1) (wv 2)
                                                  (wv 3) (wv 4) (wv 5) (wv 6) (wv 7)
                                                  (wv 8) (wv 9) (wv 10) (wv 11) (wv 12)
                                                  (base-prime))
                nil))

(defcheck group-enforce-on-curve-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-unop *fuel* 2))
                (crv-group-enforce-on-curve-gadget (wv 1) (wv 2) (wv 3) (wv 4) (base-prime))
                nil))

; enforce_in_group, and so Group::new and from_xy_coordinates: the witnessed
; quotient point (W3, W4), its on-curve products, its double, and the
; enforce_double of that double against the input, wires W3..W14 in order.
(defcheck group-enforce-in-group-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-unop *fuel* 3))
                (group-enforce-in-group-gadget (wv 1) (wv 2) (wv 3) (wv 4) (wv 5) (wv 6) (wv 7)
                                               (wv 8) (wv 9) (wv 10) (wv 11) (wv 12) (wv 13)
                                               (wv 14) (base-prime))
                nil))

(defcheck group-from-xy-coordinates-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-unop *fuel* 3))
                (grp-from-xy-coordinates-gadget (wv 1) (wv 2) (wv 3) (wv 4) (wv 5) (wv 6)
                                                (wv 7) (wv 8) (wv 9) (wv 10) (wv 11) (wv 12)
                                                (wv 13) (wv 14) (base-prime))
                nil))

(defcheck group-new-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-unop *fuel* 3))
                (literal-group-new-gadget (wv 1) (wv 2) (wv 3) (wv 4) (wv 5) (wv 6)
                                          (wv 7) (wv 8) (wv 9) (wv 10) (wv 11) (wv 12)
                                          (wv 13) (wv 14) (base-prime))
                nil))

; from_x_coordinate of W1: the ordinate is the witness W3 (W2 is unused).
(defcheck group-from-x-coordinate-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-unop *fuel* 7))
                (grp-from-x-coordinate-gadget (wv 1) (wv 3) (wv 4) (wv 5) (wv 6) (wv 7)
                                              (wv 8) (wv 9) (wv 10) (wv 11) (wv 12) (wv 13)
                                              (wv 14) (wv 15) (base-prime))
                nil))

; from_bits of n input bits: the gadget names the abscissa, the linear
; combination sum 2^i b_i, by a wire X, which is substituted by it.
(defun lebits-lc (bits i)
  (declare (xargs :measure (len bits)))
  (if (atom bits) nil (cons (list (expt 2 i) (car bits)) (lebits-lc (cdr bits) (1+ i)))))

(defconst *rc* (bits-lte-const-check-rlen (nat=>lebits* (1- (base-prime)))))

(defun group-from-bits-check (n be)
  (b* ((bits (wvs 1 n))
       (used (if (>= n 253) *rc* 0))
       (rs (wvs (1+ n) used))
       (w (+ n 1 used))
       (lc (lebits-lc (if be (rev bits) bits) 0))
       (args (list 'x (wv w) (wv (+ w 1)) (wv (+ w 2)) (wv (+ w 3)) (wv (+ w 4))
                   (wv (+ w 5)) (wv (+ w 6)) (wv (+ w 7)) (wv (+ w 8)) (wv (+ w 9))
                   (wv (+ w 10)) (wv (+ w 11)) (wv (+ w 12)))))
    (same-circuit (ext-run (acl2::circuits-h-g-from-bits *fuel* n be))
                  (if be
                      (grp-from-bits-be-gadget bits rs (nth 0 args) (nth 1 args) (nth 2 args)
                                               (nth 3 args) (nth 4 args) (nth 5 args)
                                               (nth 6 args) (nth 7 args) (nth 8 args)
                                               (nth 9 args) (nth 10 args) (nth 11 args)
                                               (nth 12 args) (nth 13 args) (base-prime))
                    (grp-from-bits-le-gadget bits rs (nth 0 args) (nth 1 args) (nth 2 args)
                                             (nth 3 args) (nth 4 args) (nth 5 args)
                                             (nth 6 args) (nth 7 args) (nth 8 args)
                                             (nth 9 args) (nth 10 args) (nth 11 args)
                                             (nth 12 args) (nth 13 args) (base-prime)))
                  (list (cons 'x lc)))))

(defcheck group-from-bits-le-extraction
  (and (group-from-bits-check 8 nil)
       (group-from-bits-check 253 nil)))

(defcheck group-from-bits-be-extraction
  (and (group-from-bits-check 8 t)
       (group-from-bits-check 253 t)))

; is_equal: is_neq and multiplier of x (W5, W6) and of y (W7, W8), and the
; AND of the two negations W9.
(defcheck group-is-equal-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-binop *fuel* 2))
                (crv-group-is-equal-gadget (wv 1) (wv 2) (wv 3) (wv 4)
                                           (wv 6) (wv 5) (wv 8) (wv 7) (wv 9) (base-prime))
                nil))

(defcheck group-is-not-equal-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-binop *fuel* 3))
                (crv-group-is-not-equal-gadget (wv 1) (wv 2) (wv 3) (wv 4)
                                               (wv 6) (wv 5) (wv 8) (wv 7) (wv 9) (base-prime))
                nil))

(defcheck group-is-zero-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-unop *fuel* 4))
                (crv-group-is-zero-gadget (wv 1) (wv 2) (wv 4) (wv 3) (wv 6) (wv 5) (wv 7)
                                          (base-prime))
                nil))

; Condition W1, first (W2, W3), second (W4, W5), output (W6, W7).
(defcheck group-ternary-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-ternary *fuel*))
                (crv-group-ternary-gadget (wv 1) (wv 2) (wv 3) (wv 4) (wv 5) (wv 6) (wv 7)
                                          (base-prime))
                nil))

; The bits of the abscissa W1 are W3..W255 (W2 is the unused ordinate).
(defcheck group-write-bits-le-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-unop *fuel* 5))
                (crv-group-write-bits-le-gadget (wv 1) (wvs 3 253) (wvs 256 *r*) 'u (base-prime))
                *u*))

(defcheck group-write-bits-be-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-unop *fuel* 5))
                (crv-group-write-bits-be-gadget (wv 1) (wvs 3 253) (wvs 256 *r*) 'u (base-prime))
                *u*))

; is_in_group: 250 constant-bit steps of 11 wires from W3, then is_zero of
; the product.
(defconst *cmul-steps*
  (b* ((k (len (cdr (grp-r-bits)))))
    (gsteps "S" k 11)))

(defcheck group-is-in-group-extraction
  (same-circuit-renamed (ext-run (acl2::circuits-h-g-unop *fuel* 6))
                        (grp-is-in-group-gadget (wv 1) (wv 2) *cmul-steps*
                                                'mx 'rx 'my 'ry 'out (base-prime))
                        (wvs 1 2) nil))

; mul by the scalar W3: Scalar::to_bits_be, the first step against the zero
; point, then 250 steps of 13 wires.
(defconst *mul-bits* (gs "B" 251))

(defcheck group-mul-extraction
  (same-circuit-renamed (ext-run (acl2::circuits-h-g-mul *fuel*))
                        (append (scalar-write-bits-le-gadget (wv 3) *mul-bits* (gs "RS" 250)
                                                             (base-prime))
                                (grp-mul-gadget (rev *mul-bits*) 'ox 'oy (gsteps "M" 250 13)
                                                (wv 1) (wv 2) (base-prime)))
                        (wvs 1 3) nil))
