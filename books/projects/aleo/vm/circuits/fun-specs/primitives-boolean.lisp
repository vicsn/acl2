; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specifications of the constraint-generating functions
; of snarkVM's circuit/types/boolean crate.
;
; A boolean is a bit (0 or 1). Constant and variable cases of each
; operation compute the same value, so modes are not parameters.
; See primitives-environment.lisp for the conventions of the primitives-* books.

(in-package "ALEOVM")

(include-book "primitives-environment")

(local (in-theory (enable spec-error fieldp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; snarkVM circuit/types/boolean/src/lib.rs: Inject::new
(define boolean-new-funspec ((value booleanp))
  :returns (b bitp)
  :short "Inject a boolean; the booleanity constraint @($(1 - a) a = 0$)
          is always satisfied by the witness."
  (if value 1 0))

; snarkVM circuit/types/boolean/src/not.rs: Not::not (helper)
(define boolean-not-funspec ((a bitp))
  :returns (b bitp)
  (if (eql a 1) 0 1))

; snarkVM circuit/types/boolean/src/and.rs: BitAnd::bitand, BitAndAssign::bitand_assign
(define boolean-and-funspec ((a bitp) (b bitp))
  :returns (c bitp)
  (if (and (eql a 1) (eql b 1)) 1 0))

; snarkVM circuit/types/boolean/src/or.rs: BitOr::bitor, BitOrAssign::bitor_assign
(define boolean-or-funspec ((a bitp) (b bitp))
  :returns (c bitp)
  (if (or (eql a 1) (eql b 1)) 1 0))

; snarkVM circuit/types/boolean/src/xor.rs: BitXor::bitxor, BitXorAssign::bitxor_assign
(define boolean-xor-funspec ((a bitp) (b bitp))
  :returns (c bitp)
  (if (eql a b) 0 1))

; snarkVM circuit/types/boolean/src/nand.rs: Nand::nand
(define boolean-nand-funspec ((a bitp) (b bitp))
  :returns (c bitp)
  (boolean-not-funspec (boolean-and-funspec a b)))

; snarkVM circuit/types/boolean/src/nor.rs: Nor::nor
(define boolean-nor-funspec ((a bitp) (b bitp))
  :returns (c bitp)
  (boolean-and-funspec (boolean-not-funspec a) (boolean-not-funspec b)))

; snarkVM circuit/types/boolean/src/equal.rs: Equal::is_not_equal
(define boolean-is-not-equal-funspec ((a bitp) (b bitp))
  :returns (c bitp)
  (boolean-xor-funspec a b))

; snarkVM circuit/types/boolean/src/equal.rs: Equal::is_equal
(define boolean-is-equal-funspec ((a bitp) (b bitp))
  :returns (c bitp)
  (boolean-not-funspec (boolean-is-not-equal-funspec a b)))

; snarkVM circuit/types/boolean/src/ternary.rs: Ternary::ternary
(define boolean-ternary-funspec ((condition bitp) (first bitp) (second bitp))
  :returns (c bitp :hyp (and (bitp first) (bitp second)))
  (if (eql condition 1) first second))

; snarkVM circuit/types/boolean/src/helpers/adder.rs: Adder::adder
(define boolean-adder-funspec ((a bitp) (b bitp) (carry bitp))
  :returns (mv (sum bitp) (carry-out bitp))
  :short "Full adder: sum bit and carry bit of @($a + b + carry$)."
  (b* ((c0 (boolean-xor-funspec a b))
       (sum (boolean-xor-funspec c0 carry))
       (c1 (boolean-and-funspec a b))
       (c2 (boolean-and-funspec carry c0)))
    (mv sum (boolean-or-funspec c1 c2))))

; snarkVM circuit/types/boolean/src/helpers/subtractor.rs: Subtractor::subtractor
(define boolean-subtractor-funspec ((a bitp) (b bitp) (borrow bitp))
  :returns (mv (difference bitp) (borrow-out bitp))
  :short "Full subtractor: difference bit and borrow bit of @($a - b - borrow$)."
  (b* ((c0 (boolean-xor-funspec a b))
       (difference (boolean-xor-funspec c0 borrow))
       (c1 (boolean-and-funspec (boolean-not-funspec a) b))
       (c2 (boolean-and-funspec borrow (boolean-not-funspec c0))))
    (mv difference (boolean-or-funspec c1 c2))))

(defruled boolean-adder-funspec-correct
  (implies (and (bitp a) (bitp b) (bitp carry))
           (mv-let (sum carry-out)
             (boolean-adder-funspec a b carry)
             (equal (+ sum (* 2 carry-out))
                    (+ a b carry))))
  :enable (boolean-adder-funspec boolean-xor-funspec boolean-and-funspec
           boolean-or-funspec bitp))

(defruled boolean-subtractor-funspec-correct
  (implies (and (bitp a) (bitp b) (bitp borrow))
           (mv-let (difference borrow-out)
             (boolean-subtractor-funspec a b borrow)
             (equal (- difference (* 2 borrow-out))
                    (- a (+ b borrow)))))
  :enable (boolean-subtractor-funspec boolean-xor-funspec boolean-and-funspec
           boolean-or-funspec boolean-not-funspec bitp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bit-list helpers

(define bits-field-sum ((bits bit-listp))
  :returns (sum fieldp)
  :short "Sum of the bits, as a base field element."
  (if (endp bits)
      0
    (pfield::add (acl2::bfix (car bits)) (bits-field-sum (cdr bits)) (base-prime)))
  :prepwork ((local (in-theory (enable fieldp)))))

; snarkVM circuit/types/boolean/src/helpers/bits_are_zero.rs: Boolean::assert_bits_are_zero
(define boolean-assert-bits-are-zero-funspec ((bits bit-listp))
  :returns (yes/no booleanp)
  :short "Assert that the field sum of the bits is zero
          (equivalently, for fewer than @(tsee base-prime) bits, all bits are 0)."
  (assert-eq-funspec (bits-field-sum bits) 0)
  :guard-hints (("Goal" :in-theory (enable fieldp pfield::fep))))

; snarkVM circuit/types/boolean/src/helpers/comparator.rs: Boolean::is_less_than_or_equal_constant
(define boolean-is-less-than-or-equal-constant-funspec
  ((circuit-bits-le bit-listp) (constant-bits-le bit-listp))
  :returns (res (or (reserrp res) (bitp res)))
  :short "Whether the little-endian bits denote a natural
          at most the one of the constant bits;
          halts if the lengths differ."
  (if (equal (len circuit-bits-le) (len constant-bits-le))
      (if (<= (acl2::lebits=>nat circuit-bits-le)
              (acl2::lebits=>nat constant-bits-le))
          1
        0)
    (spec-error)))

(define comparator-fold ((constant-bits-le bit-listp)
                         (circuit-bits-le bit-listp)
                         (rest-is-less bitp))
  :returns (res bitp :hyp (bitp rest-is-less))
  :short "The fold in @('is_less_than_or_equal_constant'), from the LSB,
          computing whether the constant is less than the circuit bits."
  (if (or (endp constant-bits-le) (endp circuit-bits-le))
      rest-is-less
    (comparator-fold (cdr constant-bits-le)
                     (cdr circuit-bits-le)
                     (if (eql (car constant-bits-le) 1)
                         (boolean-and-funspec (car circuit-bits-le) rest-is-less)
                       (boolean-or-funspec (car circuit-bits-le) rest-is-less)))))

(local
 (defruled lebits=>nat-when-consp
   (implies (consp x)
            (equal (acl2::lebits=>nat x)
                   (+ (acl2::bfix (car x))
                      (* 2 (acl2::lebits=>nat (cdr x))))))
   :use (:instance acl2::lebits=>nat-of-cons
         (acl2::lodigit (car x)) (acl2::hidigits (cdr x)))))

(defruled comparator-fold-correct
  :short "Relates the snarkVM fold to the comparison of the bits' values."
  (implies (and (bit-listp k)
                (bit-listp c)
                (equal (len k) (len c))
                (bitp acc))
           (equal (comparator-fold k c acc)
                  (if (or (< (acl2::lebits=>nat k) (acl2::lebits=>nat c))
                          (and (equal (acl2::lebits=>nat k) (acl2::lebits=>nat c))
                               (equal acc 1)))
                      1
                    0)))
  :induct (comparator-fold k c acc)
  :enable (comparator-fold boolean-and-funspec boolean-or-funspec
           lebits=>nat-when-consp bitp)
  :prep-books ((include-book "arithmetic-5/top" :dir :system)))

(defruled boolean-is-less-than-or-equal-constant-funspec-is-fold
  :short "The spec equals the negated snarkVM fold."
  (implies (and (bit-listp circuit-bits-le)
                (bit-listp constant-bits-le)
                (equal (len circuit-bits-le) (len constant-bits-le)))
           (equal (boolean-is-less-than-or-equal-constant-funspec
                   circuit-bits-le constant-bits-le)
                  (boolean-not-funspec
                   (comparator-fold constant-bits-le circuit-bits-le 0))))
  :enable (boolean-is-less-than-or-equal-constant-funspec
           boolean-not-funspec
           comparator-fold-correct))

; snarkVM circuit/types/boolean/src/helpers/comparator.rs: Boolean::assert_less_than_or_equal_constant
(define boolean-assert-less-than-or-equal-constant-funspec
  ((circuit-bits-le bit-listp) (constant-bits-le bit-listp))
  :returns (yes/no booleanp)
  (b* ((res (boolean-is-less-than-or-equal-constant-funspec circuit-bits-le
                                                            constant-bits-le)))
    (and (not (reserrp res))
         (assert-funspec res)))
  :guard-hints (("Goal" :in-theory (enable fieldp pfield::fep
                                           boolean-is-less-than-or-equal-constant-funspec))))
