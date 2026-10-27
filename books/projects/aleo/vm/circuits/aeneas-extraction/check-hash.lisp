; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

; Extraction checks for the circuit/algorithms rows whose constants are
; 253-bit field elements: the model keeps them as expressions in Cs::ks
; (here inverses and products of the Edwards coefficients), evaluated mod p.

(include-book "check-lib")
(include-book "../fun-circuits/hped-elligator2")
(include-book "../fun-circuits/hbhp-phasher")
(include-book "../fun-specs/curve-network")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *u* '((u . 1)))

(defconst *r* (bits-lt-prime-rlen (base-prime)))

; Elligator2::encode on the input W1. The gadget's wires are fresh symbols:
; the 33 named wires, one (square, product) pair per exponent bit, the 253
; root bits and the range check wires.

(defun ell2-pairs (n)
  (if (zp n)
      nil
    (cons (list (acl2::packn-pos (list "PS" n) 'wv) (acl2::packn-pos (list "PR" n) 'wv))
          (ell2-pairs (1- n)))))

(defcheck elligator2-encode-extraction
  (same-circuit-renamed
   (ext-run (acl2::circuits-h-ell2-encode *fuel*))
   (hped-ell2-gadget (wv 1)
                     (gs "E" *hped-ell2-nwires*)
                     (rev (ell2-pairs (len (hped-ell2-exp-bits))))
                     (gs "B" 253)
                     (gs "R" *r*)
                     'u)
   (list (wv 1))
   *u*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; BHPHasher::hash_uncompressed of the input bits W1..Wn with WS chunks per
; window. The bases are multiples of the generator; the model's named
; constants are their lookup tables (hbhp-tab-x, hbhp-tab-y), indexed
; 1 + 8 (w ws + j) + 2 k + xy.

(defun bhp-gens (n)
  (if (zp n)
      nil
    (append (bhp-gens (1- n))
            (list (ecurve::edwards-bls12-mul (1+ n) (curve-generator-g))))))

(defun bhp-syms-chunk (g w ws j)
  (b* ((tx (hbhp-tab-x g j))
       (ty (hbhp-tab-y g j))
       (base (+ 1 (* 8 (+ (* w ws) j)))))
    (list (cons (+ base 0) (nth 0 tx)) (cons (+ base 1) (nth 0 ty))
          (cons (+ base 2) (nth 1 tx)) (cons (+ base 3) (nth 1 ty))
          (cons (+ base 4) (nth 2 tx)) (cons (+ base 5) (nth 2 ty))
          (cons (+ base 6) (nth 3 tx)) (cons (+ base 7) (nth 3 ty)))))

(defun bhp-syms-window (g w ws j)
  (declare (xargs :measure (nfix (- (nfix ws) (nfix j)))))
  (if (or (not (natp j)) (not (natp ws)) (>= j ws))
      nil
    (append (bhp-syms-chunk g w ws j) (bhp-syms-window g w ws (1+ j)))))

(defun bhp-syms (gens w ws)
  (if (atom gens)
      nil
    (append (bhp-syms-window (car gens) w ws 0)
            (bhp-syms (cdr gens) (1+ w) ws))))

(defun bhp-sym (w j m)
  (acl2::packn-pos (list "H" w "-" j "-" m) 'wv))

(defun bhp-chunk-wires (w j)
  (list (bhp-sym w j 0) (bhp-sym w j 1) (bhp-sym w j 2) (bhp-sym w j 3) (bhp-sym w j 4)))

(defun bhp-chunks (w ws)
  (if (zp ws) nil (append (bhp-chunks w (1- ws)) (list (bhp-chunk-wires w (1- ws))))))

(defun bhp-wins (nw ws)
  (if (zp nw)
      nil
    (append (bhp-wins (1- nw) ws)
            (list (cons (bhp-chunks (1- nw) ws)
                        (gs (acl2::packn-pos (list "G" (1- nw) "-") 'wv) 8))))))

(defun bhp-check (n ws)
  (b* ((nw (ceiling n (* 3 ws)))
       (gens (bhp-gens nw)))
    (same-circuit-renamed
     (ext-run-syms (acl2::circuits-h-bhp-hash-uncompressed *fuel* n ws)
                   (bhp-syms gens 0 ws))
     (hbhp-hasher-full-gadget (wvs 1 n) (bhp-wins nw ws) gens ws (base-prime))
     (wvs 1 n)
     nil)))

(defcheck bhp-hasher-hash-uncompressed-extraction
  (and (bhp-check 15 3)
       (bhp-check 14 3)
       (bhp-check 13 2)))
