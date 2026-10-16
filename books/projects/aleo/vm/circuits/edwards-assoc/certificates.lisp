; Associativity of twisted Edwards addition
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

;; The two ideal-membership certificates for associativity, checked by
;; evaluation with the verified normaliser.
;;
;; Variables: a, d are the curve coefficients, (x1,y1), (x2,y2), (x3,y3) the
;; three points, (x4,y4) = P1+P2, (x6,y6) = P2+P3, (xl,yl) = (P1+P2)+P3 and
;; (xr,yr) = P1+(P2+P3).  The generators are the three curve equations and,
;; for each division in twisted-edwards-add, denominator * quotient -
;; numerator.  The goal for x is (xl - xr) times the six denominators used for
;; the x coordinates, likewise for y.  The cofactors are computed by
;; sage/certificate.sage.

(include-book "field-certificate")
(include-book "certificate-data")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *edwards-assoc-vars*
  '(a d x1 y1 x2 y2 x3 y3 x4 y4 x6 y6 xl xr yl yr))

(defconst *edwards-assoc-d1* '(+ 1 (* d (* x1 (* x2 (* y1 y2))))))
(defconst *edwards-assoc-d2* '(- 1 (* d (* x1 (* x2 (* y1 y2))))))
(defconst *edwards-assoc-d4* '(+ 1 (* d (* x2 (* x3 (* y2 y3))))))
(defconst *edwards-assoc-d5* '(- 1 (* d (* x2 (* x3 (* y2 y3))))))
(defconst *edwards-assoc-d3x* '(+ 1 (* d (* x4 (* x3 (* y4 y3))))))
(defconst *edwards-assoc-d3y* '(- 1 (* d (* x4 (* x3 (* y4 y3))))))
(defconst *edwards-assoc-d6x* '(+ 1 (* d (* x1 (* x6 (* y1 y6))))))
(defconst *edwards-assoc-d6y* '(- 1 (* d (* x1 (* x6 (* y1 y6))))))

(defun edwards-assoc-curve-term (x y)
  (declare (xargs :guard t))
  `(- (+ (* a (* ,x ,x)) (* ,y ,y))
      (+ 1 (* d (* (* ,x ,x) (* ,y ,y))))))

(defconst *edwards-assoc-curve-gens*
  (list (edwards-assoc-curve-term 'x1 'y1)
        (edwards-assoc-curve-term 'x2 'y2)
        (edwards-assoc-curve-term 'x3 'y3)))

(defconst *edwards-assoc-gens-x*
  (append
   (list `(- (* ,*edwards-assoc-d1* x4) (+ (* x1 y2) (* y1 x2)))
         `(- (* ,*edwards-assoc-d2* y4) (- (* y1 y2) (* a (* x1 x2))))
         `(- (* ,*edwards-assoc-d3x* xl) (+ (* x4 y3) (* y4 x3)))
         `(- (* ,*edwards-assoc-d4* x6) (+ (* x2 y3) (* y2 x3)))
         `(- (* ,*edwards-assoc-d5* y6) (- (* y2 y3) (* a (* x2 x3))))
         `(- (* ,*edwards-assoc-d6x* xr) (+ (* x1 y6) (* y1 x6))))
   *edwards-assoc-curve-gens*))

(defconst *edwards-assoc-gens-y*
  (append
   (list `(- (* ,*edwards-assoc-d1* x4) (+ (* x1 y2) (* y1 x2)))
         `(- (* ,*edwards-assoc-d2* y4) (- (* y1 y2) (* a (* x1 x2))))
         `(- (* ,*edwards-assoc-d3y* yl) (- (* y4 y3) (* a (* x4 x3))))
         `(- (* ,*edwards-assoc-d4* x6) (+ (* x2 y3) (* y2 x3)))
         `(- (* ,*edwards-assoc-d5* y6) (- (* y2 y3) (* a (* x2 x3))))
         `(- (* ,*edwards-assoc-d6y* yr) (- (* y1 y6) (* a (* x1 x6)))))
   *edwards-assoc-curve-gens*))

(defconst *edwards-assoc-goal-x*
  `(* (- xl xr)
      (* ,*edwards-assoc-d1*
         (* ,*edwards-assoc-d2*
            (* ,*edwards-assoc-d3x*
               (* ,*edwards-assoc-d4*
                  (* ,*edwards-assoc-d5* ,*edwards-assoc-d6x*)))))))

(defconst *edwards-assoc-goal-y*
  `(* (- yl yr)
      (* ,*edwards-assoc-d1*
         (* ,*edwards-assoc-d2*
            (* ,*edwards-assoc-d3y*
               (* ,*edwards-assoc-d4*
                  (* ,*edwards-assoc-d5* ,*edwards-assoc-d6y*)))))))

(defthm edwards-assoc-certificate-x
  (certificate-okp *edwards-assoc-goal-x*
                   *edwards-assoc-cofactors-x*
                   *edwards-assoc-gens-x*
                   *edwards-assoc-vars*)
  :hints (("Goal" :in-theory '((:e certificate-okp)))))

(defthm edwards-assoc-certificate-y
  (certificate-okp *edwards-assoc-goal-y*
                   *edwards-assoc-cofactors-y*
                   *edwards-assoc-gens-y*
                   *edwards-assoc-vars*)
  :hints (("Goal" :in-theory '((:e certificate-okp)))))
