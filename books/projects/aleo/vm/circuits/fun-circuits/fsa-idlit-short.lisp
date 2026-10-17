; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; IdentifierLiteral::from_bits_le and from_bits_be on fewer than 248 bits
; (circuit/types/string/src/identifier_literal/helpers/from_bits.rs).
;
; The input is padded with Boolean::constant(false) to 248 bits.  Every
; snarkVM gate folds when an operand is constant, so the constraint system
; depends on the input length.  We model snarkVM's folding exactly:
;
;   - a linear combination is (:c k), a constant, or (:v vec), a sparse
;     vector over variables (and the pseudo-variable 1);
;   - Boolean AND / OR / XOR (and.rs, or.rs, xor.rs) return an operand
;     (or its negation) when either operand is constant, and otherwise
;     allocate one private variable with one constraint;
;   - NOT is 1 - x and never allocates;
;   - Field::is_equal(sum, 0) (field/src/equal.rs) is constant when the
;     sum is constant, and otherwise allocates is_neq and the multiplier
;     with two constraints;
;   - Environment::enforce (environment/src/circuit.rs) checks a constraint
;     whose three linear combinations are all constant at synthesis time
;     (failing synthesis if it does not hold) and emits nothing; otherwise
;     it emits the constraint.  assert(b) is enforce(b, 1, 1) and
;     assert_eq(a, b) is enforce(a, 1, b).
;
; Fresh variables are taken in order from a list ws.  Each operation also
; returns the canonical witness values it assigns (an alist computed from
; the valuation), which the completeness theorems use; the constraints do
; not depend on the valuation (fsa-idlit-short-indep).
;
; The gadget is validate_identifier_bits over the 248 padded bits:
; validate_byte on each of the 31 bytes (the first with the letter check),
; then validate_trailing_nulls.  With fewer than 248 input bits there is no
; assert_bits_are_zero.

(in-package "ALEOVM")

(include-book "fsa-idlit-from-bits")
(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Linear combinations.

(defun fsa-lc-constp (x) (equal (car x) :c))

(defun fsa-lc-k (x) (ifix (cadr x)))

(defun fsa-vneg (vec p)
  (if (endp vec)
      nil
    (cons (list (pfield::neg (ifix (first (car vec))) p) (second (car vec)))
          (fsa-vneg (cdr vec) p))))

(defun fsa-lc-vec (x p)
  (if (fsa-lc-constp x)
      (if (equal (mod (fsa-lc-k x) p) 0)
          nil
        (list (list (mod (fsa-lc-k x) p) 1)))
    (cadr x)))

(defun fsa-lc-val (x asg p)
  (if (fsa-lc-constp x)
      (mod (fsa-lc-k x) p)
    (r1cs::dot-product (cadr x) asg p)))

(defun fsa-lc-add (x y p)
  (if (and (fsa-lc-constp x) (fsa-lc-constp y))
      (list :c (mod (+ (fsa-lc-k x) (fsa-lc-k y)) p))
    (list :v (append (fsa-lc-vec x p) (fsa-lc-vec y p)))))

(defun fsa-lc-neg (x p)
  (if (fsa-lc-constp x)
      (list :c (mod (- (fsa-lc-k x)) p))
    (list :v (fsa-vneg (cadr x) p))))

(defun fsa-lc-sub (x y p) (fsa-lc-add x (fsa-lc-neg y p) p))

(defun fsa-lc-var (z) (list :v (list (list 1 z))))

(defun fsa-sb-not (x p) (fsa-lc-sub '(:c 1) x p))

(defun fsa-constraint (a b c p)
  (r1cs::make-r1cs-constraint :a (fsa-lc-vec a p)
                              :b (fsa-lc-vec b p)
                              :c (fsa-lc-vec c p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Gates.  Each returns (mv out constraints ws witness-alist).

(defun fsa-sb-and (x y ws asg p)
  (cond ((fsa-lc-constp x)
         (mv (if (equal (fsa-lc-val x asg p) 1) y x) nil ws nil))
        ((fsa-lc-constp y)
         (mv (if (equal (fsa-lc-val y asg p) 1) x y) nil ws nil))
        (t (b* ((z (car ws)))
             (mv (fsa-lc-var z)
                 (list (fsa-constraint x y (fsa-lc-var z) p))
                 (cdr ws)
                 (list (cons z (pfield::mul (fsa-lc-val x asg p)
                                            (fsa-lc-val y asg p) p))))))))

(defun fsa-sb-or (x y ws asg p)
  (cond ((fsa-lc-constp x)
         (mv (if (equal (fsa-lc-val x asg p) 1) x y) nil ws nil))
        ((fsa-lc-constp y)
         (mv (if (equal (fsa-lc-val y asg p) 1) y x) nil ws nil))
        (t (b* ((z (car ws))
                (vx (fsa-lc-val x asg p))
                (vy (fsa-lc-val y asg p)))
             (mv (fsa-lc-var z)
                 (list (fsa-constraint (fsa-sb-not x p) (fsa-sb-not y p)
                                       (fsa-sb-not (fsa-lc-var z) p) p))
                 (cdr ws)
                 (list (cons z (pfield::sub (pfield::add vx vy p)
                                            (pfield::mul vx vy p) p))))))))

(defun fsa-sb-xor (x y ws asg p)
  (cond ((fsa-lc-constp x)
         (mv (if (equal (fsa-lc-val x asg p) 1) (fsa-sb-not y p) y)
             nil ws nil))
        ((fsa-lc-constp y)
         (mv (if (equal (fsa-lc-val y asg p) 1) (fsa-sb-not x p) x)
             nil ws nil))
        (t (b* ((z (car ws))
                (vx (fsa-lc-val x asg p))
                (vy (fsa-lc-val y asg p)))
             (mv (fsa-lc-var z)
                 (list (fsa-constraint (fsa-lc-add x x p) y
                                       (fsa-lc-sub (fsa-lc-add x y p)
                                                   (fsa-lc-var z) p)
                                       p))
                 (cdr ws)
                 (list (cons z (pfield::sub
                                (pfield::add vx vy p)
                                (pfield::mul 2 (pfield::mul vx vy p) p)
                                p))))))))

; Field::is_equal(delta, 0); returns NOT is_neq.
(defun fsa-sb-is-zero (delta ws asg p)
  (if (fsa-lc-constp delta)
      (mv (list :c (if (equal (fsa-lc-val delta asg p) 0) 1 0)) nil ws nil)
    (b* ((n (car ws))
         (m (cadr ws))
         (d (fsa-lc-val delta asg p)))
      (mv (fsa-sb-not (fsa-lc-var n) p)
          (list (fsa-constraint delta (fsa-lc-var m) (fsa-lc-var n) p)
                (fsa-constraint delta (fsa-sb-not (fsa-lc-var n) p)
                                '(:c 0) p))
          (cddr ws)
          (list (cons n (if (equal d 0) 0 1))
                (cons m (if (equal d 0) 1 (pfield::inv d p))))))))

; Environment::enforce; returns (mv constraints ok).
(defun fsa-enforce (a b c asg p)
  (if (and (fsa-lc-constp a) (fsa-lc-constp b) (fsa-lc-constp c))
      (mv nil (equal (pfield::mul (fsa-lc-val a asg p) (fsa-lc-val b asg p) p)
                     (fsa-lc-val c asg p)))
    (mv (list (fsa-constraint a b c p)) t)))

(defun fsa-agrees (wal asg)
  (if (endp wal)
      t
    (and (equal (lookup-equal (caar wal) asg) (cdar wal))
         (fsa-agrees (cdr wal) asg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Values of linear combinations.

(defruled fsa-dot-of-vneg
  (implies (primep p)
           (equal (r1cs::dot-product (fsa-vneg vec p) asg p)
                  (pfield::neg (r1cs::dot-product vec asg p) p)))
  :induct (fsa-vneg vec p)
  :in-theory (enable r1cs::dot-product fsa-vneg))

(defrule fsa-dot-of-lc-vec
  (implies (primep p)
           (equal (r1cs::dot-product (fsa-lc-vec x p) asg p)
                  (fsa-lc-val x asg p)))
  :enable (r1cs::dot-product pfield::mul pfield::add))

(defrule fsa-fep-of-lc-val
  (implies (primep p)
           (pfield::fep (fsa-lc-val x asg p) p))
  :enable pfield::fep)

(defrule fsa-natp-of-lc-val
  (implies (primep p)
           (and (integerp (fsa-lc-val x asg p))
                (natp (fsa-lc-val x asg p))
                (< (fsa-lc-val x asg p) p)))
  :in-theory (e/d (pfield::fep) (fsa-lc-val fsa-fep-of-lc-val))
  :use fsa-fep-of-lc-val
  :rule-classes :rewrite)

(defrule fsa-val-of-lc-add
  (implies (primep p)
           (equal (fsa-lc-val (fsa-lc-add x y p) asg p)
                  (pfield::add (fsa-lc-val x asg p) (fsa-lc-val y asg p) p)))
  :in-theory (e/d (r1cs::dot-product-of-append pfield::add) (fsa-lc-vec))
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)))

(defrule fsa-val-of-lc-neg
  (implies (primep p)
           (equal (fsa-lc-val (fsa-lc-neg x p) asg p)
                  (pfield::neg (fsa-lc-val x asg p) p)))
  :enable (fsa-dot-of-vneg pfield::neg)
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)
               (include-book "kestrel/arithmetic-light/minus" :dir :system)))

(defrule fsa-val-of-lc-sub
  (implies (primep p)
           (equal (fsa-lc-val (fsa-lc-sub x y p) asg p)
                  (pfield::sub (fsa-lc-val x asg p) (fsa-lc-val y asg p) p)))
  :in-theory (e/d (pfield::sub) (fsa-lc-val fsa-lc-add fsa-lc-neg)))

(defrule fsa-sub-k-equal-k
  (implies (and (primep p) (integerp x) (natp k) (< k p))
           (equal (equal (pfield::sub k x p) k)
                  (equal (mod x p) 0)))
  :enable (pfield::sub pfield::add pfield::neg)
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defrule fsa-val-of-lc-var
  (implies (and (primep p) (symbolp z)
                (pfield::fep (lookup-equal z asg) p))
           (equal (fsa-lc-val (fsa-lc-var z) asg p)
                  (lookup-equal z asg)))
  :enable (r1cs::dot-product pfield::fep))

(defrule fsa-val-of-lc-var-gen
  (implies (and (primep p) (symbolp z))
           (equal (fsa-lc-val (fsa-lc-var z) asg p)
                  (pfield::mul 1 (lookup-equal z asg) p)))
  :enable (r1cs::dot-product))

(defrule fsa-holds-of-constraint
  (implies (primep p)
           (equal (r1cs::r1cs-constraint-holdsp (fsa-constraint a b c p) asg p)
                  (equal (pfield::mul (fsa-lc-val a asg p) (fsa-lc-val b asg p) p)
                         (fsa-lc-val c asg p))))
  :in-theory (e/d (r1cs::r1cs-constraint-holdsp fsa-constraint)
                  (fsa-lc-vec fsa-lc-val)))

(defrule fsa-val-of-const
  (equal (fsa-lc-val (list :c k) asg p) (mod (ifix k) p)))

(defrule fsa-lc-constp-of-var
  (not (fsa-lc-constp (fsa-lc-var z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Gate semantics on Boolean operands.  -val: the output value, given the
; constraints or the canonical witnesses; -holds: the canonical witnesses
; satisfy the constraints.

(defun fsa-band (a b) (if (and (equal a 1) (equal b 1)) 1 0))
(defun fsa-bor (a b) (if (or (equal a 1) (equal b 1)) 1 0))
(defun fsa-bxor (a b) (if (equal a b) 0 1))
(defun fsa-bnot (a) (if (equal a 1) 0 1))

(defrule fsa-bitp-of-bit-ops
  (and (bitp (fsa-band a b)) (bitp (fsa-bor a b))
       (bitp (fsa-bxor a b)) (bitp (fsa-bnot a))))

(defrule fsa-sub-1-of-bit
  (implies (and (primep p) (bitp v))
           (equal (pfield::sub 1 v p) (fsa-bnot v)))
  :enable bitp)

(defrule fsa-add-k-equal-k
  (implies (and (primep p) (integerp x) (natp k) (< k p))
           (equal (equal (pfield::add k x p) k)
                  (equal (mod x p) 0)))
  :enable pfield::add
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defmacro fsa-gate-thms (name op spec)
  (let ((val (acl2::packn-pos (list name '-val) 'fsa))
        (holds (acl2::packn-pos (list name '-holds) 'fsa))
        (bitp (acl2::packn-pos (list name '-bitp) 'fsa)))
    `(progn
       (defrule ,val
         (implies (and (primep p) (< 2 p) (symbolp (car ws))
                       (bitp (fsa-lc-val x asg p))
                       (bitp (fsa-lc-val y asg p))
                       (or (r1cs::r1cs-constraints-holdp
                            (mv-nth 1 (,op x y ws asg p)) asg p)
                           (fsa-agrees (mv-nth 3 (,op x y ws asg p)) asg)))
                  (equal (fsa-lc-val (mv-nth 0 (,op x y ws asg p)) asg p)
                         (let ((a (fsa-lc-val x asg p))
                               (b (fsa-lc-val y asg p)))
                           (declare (ignorable a b))
                           ,spec)))
         :do-not-induct t
         :cases ((and (equal (fsa-lc-val x asg p) 0) (equal (fsa-lc-val y asg p) 0))
                 (and (equal (fsa-lc-val x asg p) 0) (equal (fsa-lc-val y asg p) 1))
                 (and (equal (fsa-lc-val x asg p) 1) (equal (fsa-lc-val y asg p) 0)))
         :in-theory (e/d (bitp r1cs::r1cs-constraints-holdp pfield::fep)
                         (fsa-lc-val fsa-lc-var fsa-lc-add fsa-lc-sub fsa-sb-not
                          fsa-constraint)))
       (defrule ,bitp
         (implies (and (primep p) (< 2 p) (symbolp (car ws))
                       (bitp (fsa-lc-val x asg p))
                       (bitp (fsa-lc-val y asg p))
                       (or (r1cs::r1cs-constraints-holdp
                            (mv-nth 1 (,op x y ws asg p)) asg p)
                           (fsa-agrees (mv-nth 3 (,op x y ws asg p)) asg)))
                  (bitp (fsa-lc-val (mv-nth 0 (,op x y ws asg p)) asg p)))
         :in-theory (e/d (bitp) (,op fsa-lc-val))
         :use ,val)
       (defrule ,holds
         (implies (and (primep p) (< 2 p) (symbolp (car ws))
                       (bitp (fsa-lc-val x asg p))
                       (bitp (fsa-lc-val y asg p))
                       (fsa-agrees (mv-nth 3 (,op x y ws asg p)) asg))
                  (r1cs::r1cs-constraints-holdp
                   (mv-nth 1 (,op x y ws asg p)) asg p))
         :do-not-induct t
         :cases ((and (equal (fsa-lc-val x asg p) 0) (equal (fsa-lc-val y asg p) 0))
                 (and (equal (fsa-lc-val x asg p) 0) (equal (fsa-lc-val y asg p) 1))
                 (and (equal (fsa-lc-val x asg p) 1) (equal (fsa-lc-val y asg p) 0)))
         :in-theory (e/d (bitp r1cs::r1cs-constraints-holdp pfield::fep)
                         (fsa-lc-val fsa-lc-var fsa-lc-add fsa-lc-sub fsa-sb-not
                          fsa-constraint))))))

(defrule fsa-val-of-sb-not
  (implies (primep p)
           (equal (fsa-lc-val (fsa-sb-not x p) asg p)
                  (pfield::sub 1 (fsa-lc-val x asg p) p)))
  :in-theory (e/d (pfield::sub) (fsa-lc-val fsa-lc-add fsa-lc-neg))
  :expand ((fsa-lc-val '(:c 1) asg p)))

(fsa-gate-thms fsa-sb-and fsa-sb-and (fsa-band a b))

(fsa-gate-thms fsa-sb-or fsa-sb-or (fsa-bor a b))

(fsa-gate-thms fsa-sb-xor fsa-sb-xor (fsa-bxor a b))

(defrule fsa-mul-equal-self
  (implies (and (primep p) (pfield::fep d p) (not (equal d 0)) (integerp n))
           (equal (equal (pfield::mul n d p) d)
                  (equal (mod n p) 1)))
  :use ((:instance pfield::mul-associative (x n) (y d) (z (pfield::inv d p)) (pfield::p p))
        (:instance pfield::mul-of-inv-arg2 (x d) (pfield::p p))
        (:instance fsa-mul-1 (x n)))
  :in-theory (disable pfield::mul-associative pfield::mul-of-inv-arg2
                      pfield::mul-commutative pfield::mul-commutative-2)
  :prep-lemmas
  ((defruled fsa-mul-1
     (implies (and (primep p) (integerp x))
              (equal (pfield::mul x 1 p) (mod x p)))
     :enable pfield::mul)))

(defrule fsa-sb-is-zero-val
  (implies (and (primep p) (symbolp (car ws)) (symbolp (cadr ws))
                (or (r1cs::r1cs-constraints-holdp
                     (mv-nth 1 (fsa-sb-is-zero d ws asg p)) asg p)
                    (fsa-agrees (mv-nth 3 (fsa-sb-is-zero d ws asg p)) asg)))
           (equal (fsa-lc-val (mv-nth 0 (fsa-sb-is-zero d ws asg p)) asg p)
                  (if (equal (fsa-lc-val d asg p) 0) 1 0)))
  :do-not-induct t
  :cases ((equal (fsa-lc-val d asg p) 0))
  :in-theory (e/d (r1cs::r1cs-constraints-holdp pfield::fep)
                  (fsa-lc-val fsa-lc-var fsa-lc-add fsa-lc-sub fsa-sb-not
                   fsa-constraint)))

(defrule fsa-sb-is-zero-holds
  (implies (and (primep p) (symbolp (car ws)) (symbolp (cadr ws))
                (fsa-agrees (mv-nth 3 (fsa-sb-is-zero d ws asg p)) asg))
           (r1cs::r1cs-constraints-holdp
            (mv-nth 1 (fsa-sb-is-zero d ws asg p)) asg p))
  :do-not-induct t
  :cases ((equal (fsa-lc-val d asg p) 0))
  :in-theory (e/d (r1cs::r1cs-constraints-holdp pfield::fep)
                  (fsa-lc-val fsa-lc-var fsa-lc-add fsa-lc-sub fsa-sb-not
                   fsa-constraint)))

(defrule fsa-enforce-holds-when-ok
  (implies (and (primep p) (mv-nth 1 (fsa-enforce a b c asg p)))
           (equal (r1cs::r1cs-constraints-holdp
                   (mv-nth 0 (fsa-enforce a b c asg p)) asg p)
                  (equal (pfield::mul (fsa-lc-val a asg p) (fsa-lc-val b asg p) p)
                         (fsa-lc-val c asg p))))
  :in-theory (e/d (r1cs::r1cs-constraints-holdp)
                  (fsa-lc-val fsa-constraint)))

(defrule fsa-enforce-ok-when-holds
  (implies (and (primep p)
                (r1cs::r1cs-constraints-holdp
                 (mv-nth 0 (fsa-enforce a b c asg p)) asg p))
           (equal (mv-nth 1 (fsa-enforce a b c asg p))
                  (equal (pfield::mul (fsa-lc-val a asg p) (fsa-lc-val b asg p) p)
                         (fsa-lc-val c asg p))))
  :in-theory (e/d (r1cs::r1cs-constraints-holdp)
                  (fsa-lc-val fsa-constraint)))

(defrule fsa-enforce-complete
  (implies (and (primep p)
                (equal (pfield::mul (fsa-lc-val a asg p) (fsa-lc-val b asg p) p)
                       (fsa-lc-val c asg p)))
           (and (r1cs::r1cs-constraints-holdp
                 (mv-nth 0 (fsa-enforce a b c asg p)) asg p)
                (mv-nth 1 (fsa-enforce a b c asg p))))
  :in-theory (e/d (r1cs::r1cs-constraints-holdp)
                  (fsa-lc-val fsa-constraint)))

(defrule fsa-symbol-listp-of-gate-ws
  (implies (symbol-listp ws)
           (and (symbol-listp (mv-nth 2 (fsa-sb-and x y ws asg p)))
                (symbol-listp (mv-nth 2 (fsa-sb-or x y ws asg p)))
                (symbol-listp (mv-nth 2 (fsa-sb-xor x y ws asg p)))
                (symbol-listp (mv-nth 2 (fsa-sb-is-zero d ws asg p))))))

(defruled fsa-agrees-of-append
  (equal (fsa-agrees (append a b) asg)
         (and (fsa-agrees a asg) (fsa-agrees b asg))))

(in-theory (disable fsa-sb-and fsa-sb-or fsa-sb-xor fsa-sb-is-zero fsa-enforce
                    fsa-sb-not fsa-lc-add fsa-lc-sub fsa-lc-neg fsa-lc-var
                    fsa-lc-val fsa-constraint fsa-band fsa-bor fsa-bxor
                    fsa-bnot))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; validate_byte.  bits: 8 linear combinations.  Returns
; (mv null-flag constraints ws witness-alist ok).

(defun fsa-vbyte-first (b2 b6 b4b3 b1b0 ws asg p)
  (b* (((mv partial c1 ws v1) (fsa-sb-and b4b3 b1b0 ws asg p))
       ((mv uo c2 ws v2) (fsa-sb-and partial b2 ws asg p))
       ((mv il c3 ws v3) (fsa-sb-and b6 (fsa-sb-not uo p) ws asg p))
       ((mv c4 ok) (fsa-enforce il '(:c 1) '(:c 1) asg p)))
    (mv (append c1 c2 c3 c4) ws (append v1 v2 v3) ok)))

(defun fsa-vbyte (bits first ws asg p)
  (b* ((b0 (nth 0 bits)) (b1 (nth 1 bits)) (b2 (nth 2 bits))
       (b3 (nth 3 bits)) (b4 (nth 4 bits)) (b5 (nth 5 bits))
       (b6 (nth 6 bits)) (b7 (nth 7 bits))
       ((mv cs0 ok0) (fsa-enforce b7 '(:c 1) '(:c 0) asg p))
       ((mv b4b3 cs1 ws w1) (fsa-sb-and b4 b3 ws asg p))
       ((mv b1b0 cs2 ws w2) (fsa-sb-and b1 b0 ws asg p))
       (sum (fsa-lc-add (fsa-lc-add (fsa-lc-add (fsa-lc-add b0 b1 p) b2 p)
                                    b3 p)
                        b4 p))
       ((mv az5 cs3 ws w3) (fsa-sb-is-zero sum ws asg p))
       ((mv null cs4 ws w4) (fsa-sb-and (fsa-sb-not b6 p) (fsa-sb-not b5 p)
                                        ws asg p))
       ((mv lower cs5 ws w5) (fsa-sb-and b6 b5 ws asg p))
       (upper (fsa-lc-sub b6 lower p))
       (digit (fsa-lc-sub b5 lower p))
       ((mv cs6 ok6) (fsa-enforce null (fsa-sb-not az5 p) '(:c 0) asg p))
       ((mv b2orb1 cs7 ws w7) (fsa-sb-or b2 b1 ws asg p))
       ((mv invd cs8 ws w8) (fsa-sb-and b3 b2orb1 ws asg p))
       ((mv cs9 ok9) (fsa-enforce digit
                                  (fsa-lc-add (fsa-lc-sub '(:c 1) b4 p) invd p)
                                  '(:c 0) asg p))
       ((mv x1 cs10 ws w10) (fsa-sb-xor b2 b1b0 ws asg p))
       ((mv badu cs11 ws w11) (fsa-sb-and b4b3 x1 ws asg p))
       ((mv cs12 ok12) (fsa-enforce upper (fsa-lc-add az5 badu p) '(:c 0)
                                    asg p))
       ((mv o1 cs13 ws w13) (fsa-sb-or b2 b1b0 ws asg p))
       ((mv badl cs14 ws w14) (fsa-sb-and b4b3 o1 ws asg p))
       ((mv cs15 ok15) (fsa-enforce lower (fsa-lc-add az5 badl p) '(:c 0)
                                    asg p))
       ((mv cs16 ws w16 ok16)
        (if first
            (fsa-vbyte-first b2 b6 b4b3 b1b0 ws asg p)
          (mv nil ws nil t))))
    (mv null
        (append cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 cs12 cs13
                cs14 cs15 cs16)
        ws
        (append w1 w2 w3 w4 w5 w7 w8 w10 w11 w13 w14 w16)
        (and ok0 ok6 ok9 ok12 ok15 ok16))))

; The same computation on the bit values.
(defun fsa-vbyte-vals (v first p)
  (b* ((v0 (nth 0 v)) (v1 (nth 1 v)) (v2 (nth 2 v)) (v3 (nth 3 v))
       (v4 (nth 4 v)) (v5 (nth 5 v)) (v6 (nth 6 v)) (v7 (nth 7 v))
       (ok0 (equal (pfield::mul v7 1 p) 0))
       (b4b3 (fsa-band v4 v3))
       (b1b0 (fsa-band v1 v0))
       (sum (pfield::add (pfield::add (pfield::add (pfield::add v0 v1 p) v2 p)
                                      v3 p)
                         v4 p))
       (az5 (if (equal sum 0) 1 0))
       (null (fsa-band (fsa-bnot v6) (fsa-bnot v5)))
       (lower (fsa-band v6 v5))
       (upper (pfield::sub v6 lower p))
       (digit (pfield::sub v5 lower p))
       (ok6 (equal (pfield::mul null (fsa-bnot az5) p) 0))
       (invd (fsa-band v3 (fsa-bor v2 v1)))
       (ok9 (equal (pfield::mul digit (pfield::add (fsa-bnot v4) invd p) p) 0))
       (badu (fsa-band b4b3 (fsa-bxor v2 b1b0)))
       (ok12 (equal (pfield::mul upper (pfield::add az5 badu p) p) 0))
       (badl (fsa-band b4b3 (fsa-bor v2 b1b0)))
       (ok15 (equal (pfield::mul lower (pfield::add az5 badl p) p) 0))
       (ok16 (if first
                 (equal (pfield::mul
                         (fsa-band v6 (fsa-bnot (fsa-band (fsa-band b4b3 b1b0) v2)))
                         1 p)
                        1)
               t)))
    (mv null (and ok0 ok6 ok9 ok12 ok15 ok16))))

(defun fsa-lc-vals (xs asg p)
  (if (endp xs)
      nil
    (cons (fsa-lc-val (car xs) asg p) (fsa-lc-vals (cdr xs) asg p))))

(defmacro fsa-byte-bit-hyps ()
  '(and (bitp (fsa-lc-val (nth 0 bits) asg p))
        (bitp (fsa-lc-val (nth 1 bits) asg p))
        (bitp (fsa-lc-val (nth 2 bits) asg p))
        (bitp (fsa-lc-val (nth 3 bits) asg p))
        (bitp (fsa-lc-val (nth 4 bits) asg p))
        (bitp (fsa-lc-val (nth 5 bits) asg p))
        (bitp (fsa-lc-val (nth 6 bits) asg p))
        (bitp (fsa-lc-val (nth 7 bits) asg p))))

(defmacro fsa-byte-vals ()
  '(list (fsa-lc-val (nth 0 bits) asg p) (fsa-lc-val (nth 1 bits) asg p)
         (fsa-lc-val (nth 2 bits) asg p) (fsa-lc-val (nth 3 bits) asg p)
         (fsa-lc-val (nth 4 bits) asg p) (fsa-lc-val (nth 5 bits) asg p)
         (fsa-lc-val (nth 6 bits) asg p) (fsa-lc-val (nth 7 bits) asg p)))

(defrule fsa-bitp-of-if-01
  (bitp (if c 1 0)))

(defrule fsa-val-of-c01
  (implies (and (primep p) (< 2 p))
           (and (equal (fsa-lc-val '(:c 0) asg p) 0)
                (equal (fsa-lc-val '(:c 1) asg p) 1))))

(defruled fsa-mv-nth-cons
  (and (equal (mv-nth 0 (cons a b)) a)
       (implies (posp n)
                (equal (mv-nth n (cons a b)) (mv-nth (1- n) b))))
  :enable mv-nth)

(defruled fsa-nth-cons
  (and (equal (nth 0 (cons a b)) a)
       (implies (posp n)
                (equal (nth n (cons a b)) (nth (1- n) b)))))

(defruled fsa-trivial-nil
  (and (r1cs::r1cs-constraints-holdp nil asg p)
       (fsa-agrees nil asg))
  :enable r1cs::r1cs-constraints-holdp)

(deftheory fsa-byte-semantic-rules
  '(fsa-sb-and-val fsa-sb-and-bitp fsa-sb-and-holds
    fsa-sb-or-val fsa-sb-or-bitp fsa-sb-or-holds
    fsa-sb-xor-val fsa-sb-xor-bitp fsa-sb-xor-holds
    fsa-sb-is-zero-val fsa-sb-is-zero-holds
    fsa-enforce-holds-when-ok fsa-enforce-ok-when-holds fsa-enforce-complete
    fsa-val-of-lc-add fsa-val-of-lc-sub fsa-val-of-sb-not fsa-val-of-c01
    fsa-sub-1-of-bit fsa-bitp-of-bit-ops fsa-bitp-of-if-01
    fsa-symbol-listp-of-gate-ws fsa-agrees-of-append
    acl2::symbolp-of-car-when-symbol-listp
    acl2::symbol-listp-of-cdr-when-symbol-listp
    fsa-trivial-nil fsa-mv-nth-cons fsa-nth-cons car-cons cdr-cons (:e posp) (:e binary-+)
    (:e fsa-band) (:e fsa-bor) (:e fsa-bxor) (:e fsa-bnot)
    pfield::mul-of-0-arg1 pfield::mul-of-0-arg2 (:e bitp)
    (:e primep) (:e <)))

(defruled fsa-vbyte-sound
  (implies (and (primep p) (< 2 p) (symbol-listp ws)
                (fsa-byte-bit-hyps)
                (r1cs::r1cs-constraints-holdp
                 (mv-nth 1 (fsa-vbyte bits first ws asg p)) asg p)
                (mv-nth 4 (fsa-vbyte bits first ws asg p)))
           (and (mv-nth 1 (fsa-vbyte-vals (fsa-byte-vals) first p))
                (equal (fsa-lc-val (mv-nth 0 (fsa-vbyte bits first ws asg p))
                                   asg p)
                       (mv-nth 0 (fsa-vbyte-vals (fsa-byte-vals) first p)))))
  :do-not-induct t
  :in-theory (union-theories '(fsa-vbyte fsa-vbyte-first fsa-vbyte-vals
                               r1cs::r1cs-constraints-holdp-of-append
                               fsa-byte-semantic-rules)
                             (theory 'minimal-theory)))

(defruled fsa-vbyte-complete
  (implies (and (primep p) (< 2 p) (symbol-listp ws)
                (fsa-byte-bit-hyps)
                (mv-nth 1 (fsa-vbyte-vals (fsa-byte-vals) first p))
                (fsa-agrees (mv-nth 3 (fsa-vbyte bits first ws asg p)) asg))
           (and (r1cs::r1cs-constraints-holdp
                 (mv-nth 1 (fsa-vbyte bits first ws asg p)) asg p)
                (mv-nth 4 (fsa-vbyte bits first ws asg p))
                (equal (fsa-lc-val (mv-nth 0 (fsa-vbyte bits first ws asg p))
                                   asg p)
                       (mv-nth 0 (fsa-vbyte-vals (fsa-byte-vals) first p)))))
  :do-not-induct t
  :in-theory (union-theories '(fsa-vbyte fsa-vbyte-first fsa-vbyte-vals
                               r1cs::r1cs-constraints-holdp-of-append
                               fsa-byte-semantic-rules)
                             (theory 'minimal-theory)))

(defruled fsa-vbyte-vals-spec
  (implies (and (bitp v0) (bitp v1) (bitp v2) (bitp v3)
                (bitp v4) (bitp v5) (bitp v6) (bitp v7)
                (booleanp first)
                (equal p (base-prime)))
           (b* ((v (list v0 v1 v2 v3 v4 v5 v6 v7)))
             (and (equal (mv-nth 1 (fsa-vbyte-vals v first p))
                         (not (reserrp (validate-byte v first))))
                  (implies (mv-nth 1 (fsa-vbyte-vals v first p))
                           (equal (mv-nth 0 (fsa-vbyte-vals v first p))
                                  (validate-byte v first))))))
  :in-theory '(bitp booleanp (:e fsa-vbyte-vals) (:e validate-byte)
               (:e reserrp) (:e base-prime) (:e mv-nth) (:e cons)
               (:e equal) (:e not) (:e implies)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The 31 bytes and the trailing-null chain.

(defun fsa-vrows (lcs k first ws asg p)
  (if (zp k)
      (mv nil nil ws nil t)
    (b* (((mv n c ws w ok) (fsa-vbyte lcs first ws asg p))
         ((mv ns cs ws ws2 oks) (fsa-vrows (nthcdr 8 lcs) (1- k) nil ws asg p)))
      (mv (cons n ns) (append c cs) ws (append w ws2) (and ok oks)))))

(defun fsa-trail (nulls asg p)
  (if (or (endp nulls) (endp (cdr nulls)))
      (mv nil t)
    (b* (((mv c ok1) (fsa-enforce (car nulls) (fsa-sb-not (cadr nulls) p)
                                  '(:c 0) asg p))
         ((mv cs ok2) (fsa-trail (cdr nulls) asg p)))
      (mv (append c cs) (and ok1 ok2)))))

(defruled fsa-nth-of-lc-vals
  (equal (nth i (fsa-lc-vals xs asg p))
         (if (< (nfix i) (len xs)) (fsa-lc-val (nth i xs) asg p) nil))
  :induct (nth i xs)
  :enable nth)

(defruled fsa-nthcdr-of-lc-vals
  (equal (nthcdr n (fsa-lc-vals xs asg p))
         (fsa-lc-vals (nthcdr n xs) asg p))
  :induct (nthcdr n xs)
  :enable nthcdr)

(defruled fsa-len-of-lc-vals
  (equal (len (fsa-lc-vals xs asg p)) (len xs)))

(defruled fsa-take-8
  (implies (<= 8 (len x))
           (equal (take 8 x)
                  (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x)
                        (nth 4 x) (nth 5 x) (nth 6 x) (nth 7 x))))
  :expand ((take 8 x) (take 7 (cdr x)) (take 6 (cddr x)) (take 5 (cdddr x))
           (take 4 (cddddr x)) (take 3 (cdr (cddddr x)))
           (take 2 (cddr (cddddr x))) (take 1 (cdddr (cddddr x)))
           (take 0 (cddddr (cddddr x))))
  :enable nth)

(defruled fsa-nat=>lebits-8
  (implies (and (bit-listp x) (equal (len x) 8))
           (equal (acl2::nat=>lebits 8 (lebits=>nat x)) x))
  :in-theory nil
  :use ((:instance fb-nat=>lebits-when-lebits=>nat (v (lebits=>nat x)) (bs x))))

(defruled fsa-byte-roundtrip
  (implies (and (bit-listp x) (equal (len x) 8))
           (and (equal (values-nat-to-lebits 8 (acl2::ubyte8-fix (lebits=>nat x)))
                       x)
                (acl2::ubyte8p (lebits=>nat x))))
  :enable (values-nat-to-lebits acl2::ubyte8p acl2::ubyte8-fix)
  :use (fsa-nat=>lebits-8
        (:instance values-lebits=>nat-upper-bound (bits x))))

(defruled fsa-bitp-of-nth-when-bit-listp
  (implies (and (bit-listp xs) (natp i) (< i (len xs)))
           (bitp (nth i xs)))
  :enable (bit-listp nth))

(defruled fsa-bit-listp-of-nthcdr
  (implies (bit-listp x) (bit-listp (nthcdr n x)))
  :enable (nthcdr bit-listp))

(defruled fsa-v-first-byte
  (implies (and (bit-listp v) (<= 8 (len v)))
           (and (equal (values-lebits-to-bytes v)
                       (cons (lebits=>nat (take 8 v))
                             (values-lebits-to-bytes (nthcdr 8 v))))
                (equal (values-nat-to-lebits
                        8 (acl2::ubyte8-fix (lebits=>nat (take 8 v))))
                       (list (nth 0 v) (nth 1 v) (nth 2 v) (nth 3 v)
                             (nth 4 v) (nth 5 v) (nth 6 v) (nth 7 v)))))
  :do-not-induct t
  :expand ((values-lebits-to-bytes v))
  :in-theory (disable nth bit-listp values-nat-to-lebits lebits=>nat)
  :use ((:instance fsa-byte-roundtrip (x (take 8 v)))
        (:instance fsa-take-8 (x v))))

(defruled fsa-first-byte-facts
  (implies (and (bit-listp (fsa-lc-vals bits asg p)) (<= 8 (len bits)))
           (and (equal (values-lebits-to-bytes (fsa-lc-vals bits asg p))
                       (cons (lebits=>nat (take 8 (fsa-lc-vals bits asg p)))
                             (values-lebits-to-bytes
                              (fsa-lc-vals (nthcdr 8 bits) asg p))))
                (equal (values-nat-to-lebits
                        8 (acl2::ubyte8-fix
                           (lebits=>nat (take 8 (fsa-lc-vals bits asg p)))))
                       (fsa-byte-vals))
                (fsa-byte-bit-hyps)
                (bit-listp (fsa-lc-vals (nthcdr 8 bits) asg p))))
  :do-not-induct t
  :in-theory '(fsa-nth-of-lc-vals fsa-len-of-lc-vals fsa-nthcdr-of-lc-vals
               fsa-bit-listp-of-nthcdr (:e <) (:e nfix) (:e natp))
  :use ((:instance fsa-v-first-byte (v (fsa-lc-vals bits asg p)))
        (:instance fsa-bit-listp-of-nthcdr (x (fsa-lc-vals bits asg p)) (n 8))
        (:instance fsa-bitp-of-nth-when-bit-listp (xs (fsa-lc-vals bits asg p)) (i 0))
        (:instance fsa-bitp-of-nth-when-bit-listp (xs (fsa-lc-vals bits asg p)) (i 1))
        (:instance fsa-bitp-of-nth-when-bit-listp (xs (fsa-lc-vals bits asg p)) (i 2))
        (:instance fsa-bitp-of-nth-when-bit-listp (xs (fsa-lc-vals bits asg p)) (i 3))
        (:instance fsa-bitp-of-nth-when-bit-listp (xs (fsa-lc-vals bits asg p)) (i 4))
        (:instance fsa-bitp-of-nth-when-bit-listp (xs (fsa-lc-vals bits asg p)) (i 5))
        (:instance fsa-bitp-of-nth-when-bit-listp (xs (fsa-lc-vals bits asg p)) (i 6))
        (:instance fsa-bitp-of-nth-when-bit-listp (xs (fsa-lc-vals bits asg p)) (i 7))))

(defmacro fsa-first-byte-spec ()
  '(validate-byte (values-nat-to-lebits
                   8 (acl2::ubyte8-fix
                      (lebits=>nat (take 8 (fsa-lc-vals bits asg p)))))
                  first))

(defruled fsa-vbyte-spec-sound
  (implies (and (primep p) (< 2 p) (equal p (base-prime))
                (symbol-listp ws) (booleanp first)
                (bit-listp (fsa-lc-vals bits asg p)) (<= 8 (len bits))
                (r1cs::r1cs-constraints-holdp
                 (mv-nth 1 (fsa-vbyte bits first ws asg p)) asg p)
                (mv-nth 4 (fsa-vbyte bits first ws asg p)))
           (and (not (reserrp (fsa-first-byte-spec)))
                (equal (fsa-lc-val (mv-nth 0 (fsa-vbyte bits first ws asg p))
                                   asg p)
                       (fsa-first-byte-spec))))
  :do-not-induct t
  :in-theory (theory 'minimal-theory)
  :use (fsa-first-byte-facts fsa-vbyte-sound (:instance fsa-vbyte-vals-spec
                (v0 (fsa-lc-val (nth 0 bits) asg p))
                (v1 (fsa-lc-val (nth 1 bits) asg p))
                (v2 (fsa-lc-val (nth 2 bits) asg p))
                (v3 (fsa-lc-val (nth 3 bits) asg p))
                (v4 (fsa-lc-val (nth 4 bits) asg p))
                (v5 (fsa-lc-val (nth 5 bits) asg p))
                (v6 (fsa-lc-val (nth 6 bits) asg p))
                (v7 (fsa-lc-val (nth 7 bits) asg p)))))

(defruled fsa-vbyte-spec-complete
  (implies (and (primep p) (< 2 p) (equal p (base-prime))
                (symbol-listp ws) (booleanp first)
                (bit-listp (fsa-lc-vals bits asg p)) (<= 8 (len bits))
                (not (reserrp (fsa-first-byte-spec)))
                (fsa-agrees (mv-nth 3 (fsa-vbyte bits first ws asg p)) asg))
           (and (r1cs::r1cs-constraints-holdp
                 (mv-nth 1 (fsa-vbyte bits first ws asg p)) asg p)
                (mv-nth 4 (fsa-vbyte bits first ws asg p))
                (equal (fsa-lc-val (mv-nth 0 (fsa-vbyte bits first ws asg p))
                                   asg p)
                       (fsa-first-byte-spec))))
  :do-not-induct t
  :in-theory (theory 'minimal-theory)
  :use (fsa-first-byte-facts fsa-vbyte-complete (:instance fsa-vbyte-vals-spec
                (v0 (fsa-lc-val (nth 0 bits) asg p))
                (v1 (fsa-lc-val (nth 1 bits) asg p))
                (v2 (fsa-lc-val (nth 2 bits) asg p))
                (v3 (fsa-lc-val (nth 3 bits) asg p))
                (v4 (fsa-lc-val (nth 4 bits) asg p))
                (v5 (fsa-lc-val (nth 5 bits) asg p))
                (v6 (fsa-lc-val (nth 6 bits) asg p))
                (v7 (fsa-lc-val (nth 7 bits) asg p)))))

(defruled fsa-symbol-listp-of-vbyte-ws
  (implies (symbol-listp ws)
           (symbol-listp (mv-nth 2 (fsa-vbyte bits first ws asg p))))
  :do-not-induct t
  :in-theory (union-theories '(fsa-vbyte fsa-vbyte-first
                               fsa-byte-semantic-rules)
                             (theory 'minimal-theory)))

(defruled fsa-lebits-to-bytes-step
  (implies (and (bit-listp (fsa-lc-vals bits asg p)) (<= 8 (len bits)))
           (equal (values-lebits-to-bytes (fsa-lc-vals bits asg p))
                  (cons (lebits=>nat (take 8 (fsa-lc-vals bits asg p)))
                        (values-lebits-to-bytes
                         (fsa-lc-vals (nthcdr 8 bits) asg p)))))
  :use fsa-first-byte-facts
  :in-theory nil)

(defruled fsa-bit-listp-of-lc-vals-nthcdr
  (implies (and (bit-listp (fsa-lc-vals bits asg p)) (<= 8 (len bits)))
           (bit-listp (fsa-lc-vals (nthcdr 8 bits) asg p)))
  :use fsa-first-byte-facts
  :in-theory nil)

(defruled fsa-len-of-nthcdr-8
  (implies (<= 8 (len x))
           (equal (len (nthcdr 8 x)) (- (len x) 8))))

(defruled fsa-lc-vals-when-len-0
  (implies (equal (len x) 0)
           (equal (fsa-lc-vals x asg p) nil)))

(defruled fsa-lc-vals-of-cons
  (equal (fsa-lc-vals (cons a b) asg p)
         (cons (fsa-lc-val a asg p) (fsa-lc-vals b asg p))))

(defruled fsa-null-flags-of-cons
  (equal (values-validate-bytes-null-flags (cons a b) first)
         (b* (((fty::ok flag)
               (validate-byte (values-nat-to-lebits 8 (acl2::ubyte8-fix a))
                              first))
              ((fty::ok flags) (values-validate-bytes-null-flags b nil)))
           (cons flag flags)))
  :enable values-validate-bytes-null-flags)

(defruled fsa-bitp-of-validate-byte
  (implies (not (reserrp (validate-byte bits first)))
           (bitp (validate-byte bits first)))
  :use (:instance values-bit-resultp-of-validate-byte (first-byte-p first))
  :enable values-bit-resultp
  :disable (validate-byte values-bit-resultp-of-validate-byte))

(defruled fsa-not-reserrp-of-cons-bit
  (implies (bitp a) (not (reserrp (cons a b))))
  :enable (reserrp bitp))

(defruled fsa-nil-facts
  (and (equal (values-validate-bytes-null-flags nil first) nil)
       (equal (fsa-lc-vals nil asg p) nil))
  :enable values-validate-bytes-null-flags)

(deftheory fsa-rows-rules
  '(fsa-vrows fsa-mv-nth-cons r1cs::r1cs-constraints-holdp-of-append
    fsa-agrees-of-append fsa-symbol-listp-of-vbyte-ws fsa-lc-vals-of-cons
    fsa-lebits-to-bytes-step fsa-bit-listp-of-lc-vals-nthcdr
    fsa-len-of-nthcdr-8 fsa-lc-vals-when-len-0 fsa-null-flags-of-cons
    fsa-trivial-nil car-cons cdr-cons
    (:e values-lebits-to-bytes) (:e values-validate-bytes-null-flags)
    (:e reserrp) (:e booleanp) (:e zp) (:e posp) (:e binary-+) (:e natp)
    (:e fsa-lc-vals) (:e not) (:e equal) (:e consp) (:e cons)
    (:type-prescription len) zp natp
    fsa-bitp-of-validate-byte fsa-not-reserrp-of-cons-bit fsa-nil-facts))

(defmacro fsa-rows-spec ()
  '(values-validate-bytes-null-flags
    (values-lebits-to-bytes (fsa-lc-vals bits asg p)) first))

(defruled fsa-vrows-sound
  (implies (and (primep p) (< 2 p) (equal p (base-prime))
                (symbol-listp ws) (booleanp first) (natp k)
                (equal (len bits) (* 8 k))
                (bit-listp (fsa-lc-vals bits asg p))
                (r1cs::r1cs-constraints-holdp
                 (mv-nth 1 (fsa-vrows bits k first ws asg p)) asg p)
                (mv-nth 4 (fsa-vrows bits k first ws asg p)))
           (and (not (reserrp (fsa-rows-spec)))
                (equal (fsa-lc-vals (mv-nth 0 (fsa-vrows bits k first ws asg p))
                                    asg p)
                       (fsa-rows-spec))))
  :induct (fsa-vrows bits k first ws asg p)
  :in-theory (set-difference-theories
              (union-theories '(fsa-rows-rules fsa-vbyte-spec-sound)
                              (theory 'minimal-theory))
              '(mv-nth)))

(defruled fsa-vrows-complete
  (implies (and (primep p) (< 2 p) (equal p (base-prime))
                (symbol-listp ws) (booleanp first) (natp k)
                (equal (len bits) (* 8 k))
                (bit-listp (fsa-lc-vals bits asg p))
                (not (reserrp (fsa-rows-spec)))
                (fsa-agrees (mv-nth 3 (fsa-vrows bits k first ws asg p)) asg))
           (and (r1cs::r1cs-constraints-holdp
                 (mv-nth 1 (fsa-vrows bits k first ws asg p)) asg p)
                (mv-nth 4 (fsa-vrows bits k first ws asg p))
                (equal (fsa-lc-vals (mv-nth 0 (fsa-vrows bits k first ws asg p))
                                    asg p)
                       (fsa-rows-spec))))
  :induct (fsa-vrows bits k first ws asg p)
  :in-theory (set-difference-theories
              (union-theories '(fsa-rows-rules fsa-vbyte-spec-complete)
                              (theory 'minimal-theory))
              '(mv-nth)))

(defruled fsa-mul-of-bits
  (implies (and (bitp a) (bitp b) (primep p))
           (equal (pfield::mul a b p) (* a b)))
  :enable bitp)

(defruled fsa-trail-sound
  (implies (and (primep p) (< 2 p)
                (bit-listp (fsa-lc-vals nulls asg p))
                (r1cs::r1cs-constraints-holdp
                 (mv-nth 0 (fsa-trail nulls asg p)) asg p)
                (mv-nth 1 (fsa-trail nulls asg p)))
           (equal (validate-trailing-nulls (fsa-lc-vals nulls asg p)) t))
  :induct (fsa-trail nulls asg p)
  :in-theory (e/d (validate-trailing-nulls values-b-not fsa-bnot
                   fsa-mul-of-bits r1cs::r1cs-constraints-holdp-of-append)
                  (fsa-lc-val)))

(defruled fsa-trail-complete
  (implies (and (primep p) (< 2 p)
                (bit-listp (fsa-lc-vals nulls asg p))
                (equal (validate-trailing-nulls (fsa-lc-vals nulls asg p)) t))
           (and (r1cs::r1cs-constraints-holdp
                 (mv-nth 0 (fsa-trail nulls asg p)) asg p)
                (mv-nth 1 (fsa-trail nulls asg p))))
  :induct (fsa-trail nulls asg p)
  :in-theory (e/d (validate-trailing-nulls values-b-not fsa-bnot
                   fsa-mul-of-bits r1cs::r1cs-constraints-holdp-of-append)
                  (fsa-lc-val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; from_bits_le on fewer than 248 input bits: the bits are padded to 248 with
; Boolean::constant(false), so the padding positions are constant linear
; combinations and the gates on them fold.

(defun fsa-lc-vars (wires)
  (if (endp wires)
      nil
    (cons (fsa-lc-var (car wires)) (fsa-lc-vars (cdr wires)))))

(defun fsa-short-inputs (wires)
  (append (fsa-lc-vars wires) (repeat (- 248 (len wires)) '(:c 0))))

; Returns (mv constraints witness-alist ok); ok is nil when synthesis fails on
; a constant enforce.
(defun fsa-idlit-short-le (wires ws asg p)
  (b* (((mv nulls c1 & w1 ok1)
        (fsa-vrows (fsa-short-inputs wires) 31 t ws asg p))
       ((mv c2 ok2) (fsa-trail nulls asg p)))
    (mv (append c1 c2) w1 (and ok1 ok2))))

(defruled fsa-lc-vals-of-append
  (equal (fsa-lc-vals (append x y) asg p)
         (append (fsa-lc-vals x asg p) (fsa-lc-vals y asg p))))

(defruled fsa-lc-vals-of-vars
  (implies (and (primep p) (< 2 p) (symbol-listp wires)
                (bit-listp (lookup-equal-list wires asg)))
           (equal (fsa-lc-vals (fsa-lc-vars wires) asg p)
                  (lookup-equal-list wires asg)))
  :enable (lookup-equal-list bitp pfield::fep))

(defruled fsa-lc-vals-of-repeat-0
  (implies (and (primep p) (< 2 p))
           (equal (fsa-lc-vals (repeat n '(:c 0)) asg p)
                  (repeat n 0)))
  :enable repeat)

(defruled fsa-resize-when-short
  (implies (and (bit-listp x) (natp n) (<= (len x) n))
           (equal (values-bits-resize x n)
                  (append x (repeat (- n (len x)) 0))))
  :induct (values-bits-resize x n)
  :enable (values-bits-resize repeat bit-listp))

(defruled fsa-len-of-lc-vars
  (equal (len (fsa-lc-vars wires)) (len wires)))

(defruled fsa-short-input-vals
  (implies (and (primep p) (< 2 p) (symbol-listp wires)
                (<= (len wires) 248)
                (bit-listp (lookup-equal-list wires asg)))
           (and (equal (fsa-lc-vals (fsa-short-inputs wires) asg p)
                       (values-bits-resize (lookup-equal-list wires asg) 248))
                (equal (len (fsa-short-inputs wires)) 248)))
  :do-not-induct t
  :in-theory (enable fsa-lc-vals-of-append fsa-lc-vals-of-vars
                     fsa-lc-vals-of-repeat-0 fsa-resize-when-short
                     fsa-len-of-lc-vars len-of-lookup-equal-list)
  :disable (fsa-lc-vals fsa-lc-vars values-bits-resize))

(defruled fsa-idlit-short-base-prime-facts
  (and (primep (base-prime)) (< 2 (base-prime)))
  :use primep-of-base-prime
  :in-theory '((:e base-prime) (:e <)))

(defruled fsa-idlit-short-le-sound
  (b* ((vals (lookup-equal-list wires asg))
       ((mv cs & ok) (fsa-idlit-short-le wires ws asg p)))
    (implies (and (equal p (base-prime))
                  (symbol-listp wires) (symbol-listp ws)
                  (< (len wires) 248)
                  (bit-listp vals)
                  (r1cs::r1cs-constraints-holdp cs asg p)
                  ok)
             (equal (identifier-literal-from-bits-le vals)
                    (make-identifier-literal
                     :bytes (values-lebits-to-bytes
                             (values-bits-resize vals 248))))))
  :do-not-induct t
  :in-theory (e/d (identifier-literal-from-bits-le identifier-literal-new
                   validate-identifier-bytes fsa-short-input-vals
                   r1cs::r1cs-constraints-holdp-of-append)
                  (fsa-vrows fsa-trail values-validate-bytes-null-flags
                   validate-trailing-nulls values-lebits-to-bytes
                   values-bits-resize fsa-lc-vals fsa-short-inputs))
  :use (fsa-idlit-short-base-prime-facts
        (:instance fsa-vrows-sound
                   (bits (fsa-short-inputs wires)) (k 31) (first t))
        (:instance fsa-trail-sound
                   (nulls (mv-nth 0 (fsa-vrows (fsa-short-inputs wires) 31 t
                                               ws asg p))))))

(defruled fsa-idlit-short-le-complete
  (b* ((vals (lookup-equal-list wires asg))
       ((mv cs wal ok) (fsa-idlit-short-le wires ws asg p)))
    (implies (and (equal p (base-prime))
                  (symbol-listp wires) (symbol-listp ws)
                  (< (len wires) 248)
                  (bit-listp vals)
                  (not (reserrp (identifier-literal-from-bits-le vals)))
                  (fsa-agrees wal asg))
             (and (r1cs::r1cs-constraints-holdp cs asg p)
                  ok)))
  :do-not-induct t
  :in-theory (e/d (identifier-literal-from-bits-le
                   validate-identifier-bytes fsa-short-input-vals
                   r1cs::r1cs-constraints-holdp-of-append)
                  (fsa-vrows fsa-trail values-validate-bytes-null-flags
                   validate-trailing-nulls values-lebits-to-bytes
                   values-bits-resize fsa-lc-vals fsa-short-inputs
                   identifier-literal-new))
  :use (fsa-idlit-short-base-prime-facts
        (:instance fsa-validate-ok-when-new-ok
                   (lit (make-identifier-literal
                         :bytes (values-lebits-to-bytes
                                 (values-bits-resize
                                  (lookup-equal-list wires asg) 248)))))
        (:instance fsa-vrows-complete
                   (bits (fsa-short-inputs wires)) (k 31) (first t))
        (:instance fsa-trail-complete
                   (nulls (mv-nth 0 (fsa-vrows (fsa-short-inputs wires) 31 t
                                               ws asg p))))))

; from_bits_be reverses its input and calls from_bits_le.
(defun fsa-idlit-short-be (wires ws asg p)
  (fsa-idlit-short-le (rev wires) ws asg p))

(defruled fsa-lookup-equal-list-of-rev
  (equal (lookup-equal-list (rev x) asg)
         (rev (lookup-equal-list x asg)))
  :enable (rev lookup-equal-list lookup-equal-list-of-append))

(defruled fsa-idlit-short-be-sound
  (b* ((vals (lookup-equal-list wires asg))
       ((mv cs & ok) (fsa-idlit-short-be wires ws asg p)))
    (implies (and (equal p (base-prime))
                  (symbol-listp wires) (symbol-listp ws)
                  (< (len wires) 248)
                  (bit-listp vals)
                  (r1cs::r1cs-constraints-holdp cs asg p)
                  ok)
             (equal (identifier-literal-from-bits-be vals)
                    (make-identifier-literal
                     :bytes (values-lebits-to-bytes
                             (values-bits-resize (rev vals) 248))))))
  :do-not-induct t
  :in-theory (e/d (identifier-literal-from-bits-be fsa-lookup-equal-list-of-rev)
                  (identifier-literal-from-bits-le fsa-idlit-short-le))
  :use (:instance fsa-idlit-short-le-sound (wires (rev wires))))

(defruled fsa-idlit-short-be-complete
  (b* ((vals (lookup-equal-list wires asg))
       ((mv cs wal ok) (fsa-idlit-short-be wires ws asg p)))
    (implies (and (equal p (base-prime))
                  (symbol-listp wires) (symbol-listp ws)
                  (< (len wires) 248)
                  (bit-listp vals)
                  (not (reserrp (identifier-literal-from-bits-be vals)))
                  (fsa-agrees wal asg))
             (and (r1cs::r1cs-constraints-holdp cs asg p)
                  ok)))
  :do-not-induct t
  :in-theory (e/d (identifier-literal-from-bits-be fsa-lookup-equal-list-of-rev)
                  (identifier-literal-from-bits-le fsa-idlit-short-le))
  :use (:instance fsa-idlit-short-le-complete (wires (rev wires))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The constraints, the fresh-variable supply, and the synthesis outcome do not
; depend on the assignment (only the witness alist does), so the gadget is a
; fixed constraint system per input length.

(defruled fsa-const-val-indep
  (implies (and (syntaxp (not (equal asg ''nil)))
                (fsa-lc-constp x))
           (equal (fsa-lc-val x asg p) (fsa-lc-val x nil p)))
  :enable (fsa-lc-val fsa-lc-constp))

(defun fsa-indep-conjuncts (gate idxs)
  (declare (xargs :mode :program))
  (if (endp idxs)
      nil
    (cons `(equal (mv-nth ,(car idxs) ,(append gate '(asg p)))
                  (mv-nth ,(car idxs) ,(append gate '(nil p))))
          (fsa-indep-conjuncts gate (cdr idxs)))))

(defmacro fsa-indep-thm (name gate idxs)
  `(defruled ,name
     (implies (syntaxp (not (equal asg ''nil)))
              (and ,@(fsa-indep-conjuncts gate idxs)))
     :enable (,(car gate) fsa-const-val-indep)))

(fsa-indep-thm fsa-sb-and-indep (fsa-sb-and x y ws) (0 1 2))
(fsa-indep-thm fsa-sb-or-indep (fsa-sb-or x y ws) (0 1 2))
(fsa-indep-thm fsa-sb-xor-indep (fsa-sb-xor x y ws) (0 1 2))
(fsa-indep-thm fsa-sb-is-zero-indep (fsa-sb-is-zero d ws) (0 1 2))
(fsa-indep-thm fsa-enforce-indep (fsa-enforce a b c) (0 1))

(deftheory fsa-indep-rules
  '(fsa-sb-and-indep fsa-sb-or-indep fsa-sb-xor-indep fsa-sb-is-zero-indep
    fsa-enforce-indep fsa-mv-nth-cons car-cons cdr-cons (:e posp)
    (:e binary-+)))

(defruled fsa-vbyte-indep
  (implies (syntaxp (not (equal asg ''nil)))
           (and (equal (mv-nth 0 (fsa-vbyte bits first ws asg p))
                       (mv-nth 0 (fsa-vbyte bits first ws nil p)))
                (equal (mv-nth 1 (fsa-vbyte bits first ws asg p))
                       (mv-nth 1 (fsa-vbyte bits first ws nil p)))
                (equal (mv-nth 2 (fsa-vbyte bits first ws asg p))
                       (mv-nth 2 (fsa-vbyte bits first ws nil p)))
                (equal (mv-nth 4 (fsa-vbyte bits first ws asg p))
                       (mv-nth 4 (fsa-vbyte bits first ws nil p)))))
  :do-not-induct t
  :in-theory (union-theories '(fsa-vbyte fsa-vbyte-first fsa-indep-rules)
                             (theory 'minimal-theory)))

(defruled fsa-vrows-indep
  (implies (syntaxp (not (equal asg ''nil)))
           (and (equal (mv-nth 0 (fsa-vrows lcs k first ws asg p))
                       (mv-nth 0 (fsa-vrows lcs k first ws nil p)))
                (equal (mv-nth 1 (fsa-vrows lcs k first ws asg p))
                       (mv-nth 1 (fsa-vrows lcs k first ws nil p)))
                (equal (mv-nth 2 (fsa-vrows lcs k first ws asg p))
                       (mv-nth 2 (fsa-vrows lcs k first ws nil p)))
                (equal (mv-nth 4 (fsa-vrows lcs k first ws asg p))
                       (mv-nth 4 (fsa-vrows lcs k first ws nil p)))))
  :induct (fsa-vrows lcs k first ws asg p)
  :in-theory (e/d (fsa-vbyte-indep fsa-vrows) (fsa-vbyte)))

(defruled fsa-trail-indep
  (implies (syntaxp (not (equal asg ''nil)))
           (and (equal (mv-nth 0 (fsa-trail nulls asg p))
                       (mv-nth 0 (fsa-trail nulls nil p)))
                (equal (mv-nth 1 (fsa-trail nulls asg p))
                       (mv-nth 1 (fsa-trail nulls nil p)))))
  :induct (fsa-trail nulls asg p)
  :in-theory (e/d (fsa-enforce-indep fsa-trail) (fsa-enforce)))

(defruled fsa-idlit-short-indep
  (and (equal (mv-nth 0 (fsa-idlit-short-le wires ws asg p))
              (mv-nth 0 (fsa-idlit-short-le wires ws nil p)))
       (equal (mv-nth 2 (fsa-idlit-short-le wires ws asg p))
              (mv-nth 2 (fsa-idlit-short-le wires ws nil p)))
       (equal (mv-nth 0 (fsa-idlit-short-be wires ws asg p))
              (mv-nth 0 (fsa-idlit-short-be wires ws nil p)))
       (equal (mv-nth 2 (fsa-idlit-short-be wires ws asg p))
              (mv-nth 2 (fsa-idlit-short-be wires ws nil p))))
  :cases ((equal asg nil))
  :in-theory (e/d (fsa-vrows-indep fsa-trail-indep)
                  (fsa-vrows fsa-trail fsa-short-inputs)))
