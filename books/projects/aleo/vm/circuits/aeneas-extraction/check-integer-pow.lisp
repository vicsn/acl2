; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Extraction checks for Integer pow_wrapped, pow_checked and pow: an n-bit
; base x (W1..Wn) and an m-bit unsigned exponent (W(n+1)..W(n+m)). The
; gadgets' internal wires are fresh symbols, one record per exponent bit
; after the first, matched to the extracted wires by renaming.

(include-book "check-lib")
(include-book "../fun-circuits/int-mulpow-pow-wrapped")
(include-book "../fun-circuits/int-mulpow-pow-checked")
(include-book "../fun-circuits/int-mulpow-pow-checked-128")
(include-book "../fun-circuits/int-mulpow-pow-checked-signed")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *one* '((one . 1)))

; A record: SHAPE lists, per field, 0 for a wire or the length of a list.
(defun pow-rec (prefix shape i)
  (if (atom shape)
      nil
    (cons (if (zp (car shape))
              (acl2::packn-pos (list prefix "-" i) 'wv)
            (gs (acl2::packn-pos (list prefix "-" i "-") 'wv) (car shape)))
          (pow-rec prefix (cdr shape) (1+ i)))))

(defun pow-recs (prefix shape k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      nil
    (append (pow-recs prefix shape (1- k))
            (list (pow-rec (acl2::packn-pos (list prefix (1- k)) 'wv) shape 0)))))

(defun h1 (n) (1+ (floor n 2)))

(defun pw-shape (n) (list 0 0 0 n (h1 n) 0 0 0 n (h1 n) n))
(defun pc-shape (n) (list 0 0 0 n (h1 n) n 0 0 0 0 n))
(defconst *pc128-shape* (list 0 0 0 128 65 128 0 0 0 65 128 0 0 0))

(defun sp-shape-aux (lens i k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      nil
    (cons (or (cdr (assoc i lens)) 0) (sp-shape-aux lens (1+ i) (1- k)))))

; The 46 fields of a signed step record; the lists are those of
; int-mulpow-sp-rec-okp.
(defun sp-shape (n)
  (b* ((lens (list (cons 0 n) (cons 1 n) (cons 3 n) (cons 4 n) (cons 9 n) (cons 10 n)
                   (cons 11 (h1 n)) (cons 13 (- n 2)) (cons 18 n) (cons 20 n) (cons 21 n)
                   (cons 22 n) (cons 24 n) (cons 25 n) (cons 27 n) (cons 31 (h1 n))
                   (cons 35 (- n 2)) (cons 43 n) (cons 45 n))))
    (sp-shape-aux lens 0 46)))

(defun pow-gadget (n signed m checked)
  (b* ((xs (wvs 1 n))
       (es (wvs (1+ n) m))
       (p (base-prime))
       (k (1- m)))
    (cond ((not checked)
           (int-pow-wrapped-gadget xs es (gs "P" n) (gs "PH" (h1 n)) (gs "R" n)
                                   (pow-recs "S" (pw-shape n) k) 'one p))
          (signed
           (int-pow-checked-signed-gadget xs es (gs "AX" n) (gs "MX" n) 'cx (gs "P" n)
                                          (gs "FC" (h1 n)) 'mult 'isneq (gs "LW" (- n 2))
                                          'po 'tt 'u 'v 'o1 'o2 'out (gs "NP" n) 'nz
                                          (gs "Z" n) (gs "R" n)
                                          (pow-recs "S" (sp-shape n) k) 'one p))
          ((equal n 128)
           (int-pow-checked-unsigned-128-gadget xs es (gs "P" 128) (gs "FC" 65) 'mult 'isneq
                                                'out (gs "R" 128)
                                                (pow-recs "S" *pc128-shape* k) 'one p))
          (t
           (int-pow-checked-unsigned-gadget xs es (gs "P" n) 'mult 'isneq 'out (gs "R" n)
                                            (pow-recs "S" (pc-shape n) k) 'one p)))))

(defun pow-check (n signed m checked)
  (same-circuit-renamed (ext-run (acl2::circuits-h-i-pow *fuel* n signed m (if checked 1 0)))
                        (pow-gadget n signed m checked)
                        (wvs 1 (+ n m)) *one*))

(defun pow-checks (ns signed m checked)
  (if (atom ns)
      t
    (and (pow-check (car ns) signed m checked)
         (pow-checks (cdr ns) signed m checked))))

(defconst *widths* '(8 16 32 64 128))

; Exponents of 8 bits (u8); the loop does not depend on the width of the
; exponent beyond its length.
(defcheck int-pow-wrapped-unsigned-extraction (pow-checks *widths* nil 8 nil))
(defcheck int-pow-wrapped-signed-extraction (pow-checks *widths* t 8 nil))
(defcheck int-pow-checked-unsigned-extraction (pow-checks *widths* nil 8 t))
(defcheck int-pow-checked-signed-extraction (pow-checks *widths* t 8 t))

