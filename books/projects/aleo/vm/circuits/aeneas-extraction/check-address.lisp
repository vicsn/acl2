; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Extraction checks for circuit/types/address. Address wraps Group: is_equal,
; is_not_equal, ternary, the bits, new, from_bits and from_field are the
; Group circuits, so they run the Group harnesses against the address
; gadgets. Address (W1, W2), second address (W3, W4).

(include-book "check-lib")
(include-book "../fun-circuits/crv-equal")
(include-book "../fun-circuits/crv-ternary")
(include-book "../fun-circuits/crv-bits")
(include-book "../fun-circuits/crv-compare")
(include-book "../fun-circuits/crv-project")
(include-book "../fun-circuits/fsa-address-from")
(include-book "../fun-circuits/literal-new-r1cs")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *u* '((u . 1)))

(defconst *r* (bits-lt-prime-rlen (base-prime)))

(defun address-compare-check (op)
  (b* ((ext (ext-run (acl2::circuits-h-a-compare *fuel* op)))
       (xs1 (gs "XA" 253)) (xrs1 (gs "RA" *r*))
       (xs2 (gs "XB" 253)) (xrs2 (gs "RB" *r*))
       (ds (gs "D" 253)) (rs (gs "L" 253))
       (gadget (case op
                 (0 (crv-address-is-less-than-gadget (wv 1) xs1 xrs1 (wv 3) xs2 xrs2 ds rs 'u
                                                     (base-prime)))
                 (1 (crv-address-is-greater-than-gadget (wv 1) xs1 xrs1 (wv 3) xs2 xrs2 ds rs 'u
                                                        (base-prime)))
                 (2 (crv-address-is-less-than-or-equal-gadget (wv 1) xs1 xrs1 (wv 3) xs2 xrs2 ds
                                                              rs 'u (base-prime)))
                 (t (crv-address-is-greater-than-or-equal-gadget (wv 1) xs1 xrs1 (wv 3) xs2 xrs2
                                                                 ds rs 'u (base-prime))))))
    (same-circuit-renamed ext gadget (wvs 1 4) *u*)))

(defcheck address-is-less-than-extraction (address-compare-check 0))
(defcheck address-is-greater-than-extraction (address-compare-check 1))
(defcheck address-is-less-than-or-equal-extraction (address-compare-check 2))
(defcheck address-is-greater-than-or-equal-extraction (address-compare-check 3))

(defcheck address-is-equal-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-binop *fuel* 2))
                (crv-address-is-equal-gadget (wv 1) (wv 2) (wv 3) (wv 4)
                                             (wv 6) (wv 5) (wv 8) (wv 7) (wv 9) (base-prime))
                nil))

(defcheck address-is-not-equal-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-binop *fuel* 3))
                (crv-address-is-not-equal-gadget (wv 1) (wv 2) (wv 3) (wv 4)
                                                 (wv 6) (wv 5) (wv 8) (wv 7) (wv 9) (base-prime))
                nil))

; Condition W1, first (W2, W3), second (W4, W5), output (W6, W7).
(defcheck address-ternary-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-ternary *fuel*))
                (crv-address-ternary-gadget (wv 1) (wv 2) (wv 3) (wv 4) (wv 5) (wv 6) (wv 7)
                                            (base-prime))
                nil))

(defcheck address-write-bits-le-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-unop *fuel* 5))
                (crv-address-write-bits-le-gadget (wv 1) (wvs 3 253) (wvs 256 *r*) 'u (base-prime))
                *u*))

(defcheck address-write-bits-be-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-unop *fuel* 5))
                (crv-address-write-bits-be-gadget (wv 1) (wvs 3 253) (wvs 256 *r*) 'u (base-prime))
                *u*))

; Address::new is Group::new, which is enforce_in_group on (W1, W2).
(defcheck address-new-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-unop *fuel* 3))
                (literal-group-new-gadget (wv 1) (wv 2) (wv 3) (wv 4) (wv 5) (wv 6)
                                          (wv 7) (wv 8) (wv 9) (wv 10) (wv 11) (wv 12)
                                          (wv 13) (wv 14) (base-prime))
                nil))

; from_field is from_x_coordinate of W1; the ordinate witness is W3.
(defcheck address-from-field-extraction
  (same-circuit (ext-run (acl2::circuits-h-g-unop *fuel* 7))
                (grp-from-x-coordinate-gadget (wv 1) (wv 3) (wv 4) (wv 5) (wv 6) (wv 7)
                                              (wv 8) (wv 9) (wv 10) (wv 11) (wv 12) (wv 13)
                                              (wv 14) (wv 15) (base-prime))
                nil))

; from_bits: as for Group, the abscissa wire X of the gadget is the linear
; combination of the bits.
(defun lebits-lc (bits i)
  (declare (xargs :measure (len bits)))
  (if (atom bits) nil (cons (list (expt 2 i) (car bits)) (lebits-lc (cdr bits) (1+ i)))))

(defun address-from-bits-check (n be)
  (b* ((bits (wvs 1 n))
       (lc (lebits-lc (if be (rev bits) bits) 0))
       (w (+ n 1))
       (gadget (if be
                   (grp-from-bits-be-gadget bits nil 'x (wv w) (wv (+ w 1)) (wv (+ w 2))
                                            (wv (+ w 3)) (wv (+ w 4)) (wv (+ w 5)) (wv (+ w 6))
                                            (wv (+ w 7)) (wv (+ w 8)) (wv (+ w 9)) (wv (+ w 10))
                                            (wv (+ w 11)) (wv (+ w 12)) (base-prime))
                 (grp-from-bits-le-gadget bits nil 'x (wv w) (wv (+ w 1)) (wv (+ w 2))
                                          (wv (+ w 3)) (wv (+ w 4)) (wv (+ w 5)) (wv (+ w 6))
                                          (wv (+ w 7)) (wv (+ w 8)) (wv (+ w 9)) (wv (+ w 10))
                                          (wv (+ w 11)) (wv (+ w 12)) (base-prime)))))
    (same-circuit (ext-run (acl2::circuits-h-g-from-bits *fuel* n be))
                  gadget (list (cons 'x lc)))))

(defcheck address-from-bits-le-extraction
  (and (address-from-bits-check 8 nil)
       (address-from-bits-check 252 nil)))

(defcheck address-from-bits-be-extraction
  (and (address-from-bits-check 8 t)
       (address-from-bits-check 252 t)))

; Address::from(Group) and Field::from(Address) emit nothing.
(defcheck address-from-extraction
  (same-circuit (ext-run (acl2::circuits-h-a-convert *fuel* 1)) nil nil))

(defcheck address-to-field-extraction
  (same-circuit (ext-run (acl2::circuits-h-a-convert *fuel* 0))
                (crv-address-to-field-gadget)
                nil))
