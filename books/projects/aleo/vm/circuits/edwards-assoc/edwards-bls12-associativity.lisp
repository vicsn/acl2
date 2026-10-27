; Associativity of twisted Edwards addition
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

;; Associativity of edwards-bls12-add, from the generic theorem.

(include-book "twisted-edwards-associativity")
(include-book "projects/bls12-377-curves/ecurve/edwards-bls12" :dir :system)

(defrule edwards-bls12-add-associative
  (implies (and (edwards-bls12-pointp point1)
                (edwards-bls12-pointp point2)
                (edwards-bls12-pointp point3))
           (equal (edwards-bls12-add (edwards-bls12-add point1 point2) point3)
                  (edwards-bls12-add point1 (edwards-bls12-add point2 point3))))
  :enable (edwards-bls12-add edwards-bls12-pointp))
