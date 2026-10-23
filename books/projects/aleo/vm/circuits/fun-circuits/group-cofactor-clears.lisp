; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The hypothesis edwards-bls12-cofactor-clears is a theorem: the
; Edwards-BLS12 group has order 4r or 8r and no point of order 8, so
; 4 r Q = 0 for every point Q (see ../edwards-order/group-order.lisp).

(in-package "ALEOVM")

(include-book "group-inject-sound")
(include-book "../edwards-order/group-order")

(defrule edwards-bls12-cofactor-clears-holds
  (edwards-bls12-cofactor-clears)
  :use (:instance ecurve::edwards-bls12-r-pointp-of-4q
                  (q (edwards-bls12-cofactor-clears-witness)))
  :in-theory '(edwards-bls12-cofactor-clears))
