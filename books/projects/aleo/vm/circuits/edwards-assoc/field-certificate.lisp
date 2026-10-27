; Associativity of twisted Edwards addition
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

;; Checking ideal-membership certificates over a prime field.
;;
;; A certificate is a goal term g, generator terms g_1..g_n, and cofactor
;; terms k_1..k_n, all polynomial terms in the sense of dm::polyp.  If
;; g - (k_1 g_1 + ... + k_n g_n) normalises to 0 under the verified sparse
;; Horner normaliser of projects/shnf, then g is 0 in the prime field at every
;; point where all the g_i are 0.

(include-book "projects/shnf/top" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Evaluation of a polynomial term in the prime field of p.

(defun evalf-pow (base k p)
  (declare (xargs :verify-guards nil))
  (if (zp k)
      (mod 1 p)
    (mul base (evalf-pow base (1- k) p) p)))

(defun evalf (x alist p)
  (declare (xargs :verify-guards nil))
  (if (integerp x)
      (mod x p)
    (if (atom x)
        (mod (ifix (cdr (assoc x alist))) p)
      (let ((y (cadr x)) (z (caddr x)))
        (case (car x)
          (+ (add (evalf y alist p) (evalf z alist p) p))
          (- (if (cddr x)
                 (sub (evalf y alist p) (evalf z alist p) p)
               (neg (evalf y alist p) p)))
          (* (mul (evalf y alist p) (evalf z alist p) p))
          (expt (evalf-pow (evalf y alist p) (nfix z) p))
          (otherwise 0))))))

(defthm fep-of-evalf
  (implies (posp p)
           (fep (evalf x alist p) p))
  :hints (("Goal" :in-theory (enable fep))))

(local
 (defthm integerp-of-assoc-pairlis$
   (implies (and (dm::all-integers vals)
                 (<= (len vars) (len vals))
                 (member-equal x vars))
            (integerp (cdr (assoc-equal x (pairlis$ vars vals)))))))

(local
 (defthm integerp-of-evalp
   (implies (and (dm::distinct-symbols vars)
                 (dm::all-integers vals)
                 (<= (len vars) (len vals))
                 (dm::polyp x vars))
            (integerp (dm::evalp x (pairlis$ vars vals))))
   :hints (("Goal" :use dm::integerp-evalp))))

(local
 (defun term-induct (x)
   (if (atom x)
       t
     (list (term-induct (cadr x))
           (term-induct (caddr x))))))

(local
 (defthmd mod-of-+-to-add
   (implies (and (integerp x) (integerp y) (posp p))
            (equal (mod (+ x y) p)
                   (add (mod x p) (mod y p) p)))
   :hints (("Goal" :in-theory (enable add)))))

(local
 (defthmd mod-of-+-of-minus-to-add
   (implies (and (integerp x) (integerp y) (posp p))
            (equal (mod (+ x (- y)) p)
                   (add (mod x p) (neg (mod y p) p) p)))
   :hints (("Goal" :in-theory (enable add neg)))))

(local
 (defthmd mod-of-*-to-mul
   (implies (and (integerp x) (integerp y) (posp p))
            (equal (mod (* x y) p)
                   (mul (mod x p) (mod y p) p)))
   :hints (("Goal" :in-theory (enable mul)))))

(local
 (defthmd mod-of-minus-to-neg
   (implies (and (integerp x) (posp p))
            (equal (mod (- x) p)
                   (neg (mod x p) p)))
   :hints (("Goal" :in-theory (enable neg)))))

(local
 (defthm integerp-of-expt-when-natp
   (implies (and (integerp x) (natp k))
            (integerp (expt x k)))))

(local
 (defthmd mod-of-expt-to-evalf-pow
   (implies (and (integerp x) (natp k) (posp p))
            (equal (mod (expt x k) p)
                   (evalf-pow (mod x p) k p)))
   :hints (("Goal"
            :induct (evalf-pow x k p)
            :in-theory (enable mul acl2::pos-fix)))))

(defthm evalf-is-mod-of-evalp
  (implies (and (posp p)
                (dm::distinct-symbols vars)
                (dm::all-integers vals)
                (<= (len vars) (len vals))
                (dm::polyp x vars))
           (equal (evalf x (pairlis$ vars vals) p)
                  (mod (dm::evalp x (pairlis$ vars vals)) p)))
  :hints (("Goal"
           :induct (term-induct x)
           :in-theory (e/d (mod-of-+-of-minus-to-add
                            mod-of-+-to-add
                            mod-of-*-to-mul
                            mod-of-minus-to-neg
                            mod-of-expt-to-evalf-pow)
                           (add mul neg evalf-pow)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The term k_1 g_1 + ... + k_n g_n.

(defun lincomb (cofs gens)
  (declare (xargs :guard (and (true-listp cofs) (true-listp gens))))
  (if (or (endp cofs) (endp gens))
      0
    (list '+
          (list '* (car cofs) (car gens))
          (lincomb (cdr cofs) (cdr gens)))))

(defun gens-zerop (gens alist p)
  (declare (xargs :verify-guards nil))
  (if (endp gens)
      t
    (and (equal (evalf (car gens) alist p) 0)
         (gens-zerop (cdr gens) alist p))))

(defthm evalf-of-lincomb-when-gens-zerop
  (implies (and (gens-zerop gens alist p)
                (posp p))
           (equal (evalf (lincomb cofs gens) alist p)
                  0)))

;; The check, run by evaluation on concrete certificates.

(defun certificate-okp (goal cofs gens vars)
  (declare (xargs :guard (and (true-listp cofs) (true-listp gens))
                  :verify-guards nil))
  (let ((comb (lincomb cofs gens)))
    (and (dm::distinct-symbols vars)
         (dm::polyp goal vars)
         (dm::polyp comb vars)
         (equal (dm::norm (list '- goal comb) vars) 0))))

(local
 (defthmd certificate-okp-implies-evalp-zero
   (implies (and (certificate-okp goal cofs gens vars)
                 (dm::all-integers vals)
                 (<= (len vars) (len vals)))
            (equal (dm::evalp (list '- goal (lincomb cofs gens))
                              (pairlis$ vars vals))
                   0))
   :hints (("Goal"
            :use ((:instance dm::evalh-norm
                             (dm::x (list '- goal (lincomb cofs gens)))
                             (dm::vars vars)
                             (dm::vals vals)))
            :in-theory (e/d (certificate-okp)
                            (dm::evalh-norm dm::norm dm::evalp lincomb))))))

(local
 (defthmd certificate-okp-implies-evalf-zero
   (implies (and (certificate-okp goal cofs gens vars)
                 (dm::all-integers vals)
                 (<= (len vars) (len vals))
                 (posp p))
            (equal (evalf (list '- goal (lincomb cofs gens))
                          (pairlis$ vars vals)
                          p)
                   0))
   :hints (("Goal"
            :use (certificate-okp-implies-evalp-zero
                  (:instance evalf-is-mod-of-evalp
                             (x (list '- goal (lincomb cofs gens)))))
            :in-theory (e/d (certificate-okp)
                            (evalf-is-mod-of-evalp dm::norm dm::evalp
                                                   evalf lincomb))))))

(defthm certificate-okp-sound
  (implies (and (certificate-okp goal cofs gens vars)
                (dm::all-integers vals)
                (<= (len vars) (len vals))
                (posp p)
                (gens-zerop gens (pairlis$ vars vals) p))
           (equal (evalf goal (pairlis$ vars vals) p)
                  0))
  :rule-classes nil
  :hints (("Goal"
           :use (certificate-okp-implies-evalf-zero
                 (:instance evalf-of-lincomb-when-gens-zerop
                            (alist (pairlis$ vars vals))))
           :expand ((evalf (list '- goal (lincomb cofs gens))
                           (pairlis$ vars vals)
                           p))
           :in-theory (e/d (pfield::sub-of-0)
                           (certificate-okp
                            evalf-of-lincomb-when-gens-zerop
                            evalf lincomb sub)))))
