; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; snarkVM's Group::generator is a point of order r, so values-group-generator
; is that point and not the fallback zero of values-to-group.
; r G = 0 is checked by executing a double-and-add multiplication.

(in-package "ALEOVM")

(include-book "../fun-specs/values-helpers")
(include-book "../edwards-order/basics")
(include-book "../edwards-order/bls12-points")

(defconst *progx-generator-x*
  1540945439182663264862696551825005342995406165131907382295858612069623286213)

(defconst *progx-generator-y*
  8003546896475222703853313610036801932325312921786952001586936882361378122196)

(defruled progx-generator-on-curve
  (ecurve::point-on-twisted-edwards-p
   (ecurve::point-finite *progx-generator-x* *progx-generator-y*)
   (ecurve::edwards-bls12-curve))
  :in-theory '((:e ecurve::point-on-twisted-edwards-p)
               (:e ecurve::edwards-bls12-curve)
               (:e ecurve::point-finite)))

(defruled progx-r-kills-generator-exec
  (equal (ecurve::te-mul-fast-exec
          (ecurve::edwards-bls12-r)
          (ecurve::point-finite *progx-generator-x* *progx-generator-y*)
          (ecurve::edwards-bls12-curve))
         (ecurve::twisted-edwards-zero))
  :in-theory '((:e ecurve::te-mul-fast-exec)
               (:e ecurve::edwards-bls12-r)
               (:e ecurve::edwards-bls12-curve)
               (:e ecurve::point-finite)
               (:e ecurve::twisted-edwards-zero)))

(defruled progx-r-kills-generator
  (equal (ecurve::twisted-edwards-mul
          (ecurve::edwards-bls12-r)
          (ecurve::point-finite *progx-generator-x* *progx-generator-y*)
          (ecurve::edwards-bls12-curve))
         (ecurve::twisted-edwards-zero))
  :use (progx-r-kills-generator-exec
        progx-generator-on-curve
        (:instance ecurve::twisted-edwards-mul-is-exec
                   (scalar (ecurve::edwards-bls12-r))
                   (point (ecurve::point-finite *progx-generator-x*
                                                *progx-generator-y*))
                   (curve (ecurve::edwards-bls12-curve))))
  :in-theory '(ecurve::edwards-bls12-curve-completep
               (:e ecurve::pointp)
               (:e ecurve::point-finite)
               (:e natp) (:e ecurve::edwards-bls12-r)))

(defruled progx-groupp-of-generator-point
  (groupp (ecurve::point-finite *progx-generator-x* *progx-generator-y*))
  :use (progx-r-kills-generator
        progx-generator-on-curve
        (:instance ecurve::twisted-edwards-point-orderp-when-prime-kills
                   (point (ecurve::point-finite *progx-generator-x*
                                                *progx-generator-y*))
                   (curve (ecurve::edwards-bls12-curve))
                   (r (ecurve::edwards-bls12-r))))
  :in-theory '(groupp
               ecurve::edwards-bls12-r-pointp
               ecurve::edwards-bls12-pointp
               ecurve::edwards-bls12-curve-completep
               ecurve::primep-of-edwards-bls12-r
               (:e ecurve::pointp)
               (:e ecurve::point-finite)
               (:e ecurve::twisted-edwards-zero)
               (:e equal)))

(defruled progx-values-group-generator-is-point
  (equal (values-group-generator)
         (ecurve::point-finite *progx-generator-x* *progx-generator-y*))
  :use progx-groupp-of-generator-point
  :in-theory '(values-group-generator values-to-group))
