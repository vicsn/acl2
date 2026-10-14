; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS specifications of the boolean full adder and full subtractor.
;
; snarkVM circuit/types/boolean/src/helpers/adder.rs
;   c0  = a xor b
;   sum = c0 xor carry
;   c1  = a and b
;   c2  = carry and c0
;   carry_out = c1 or c2
;
; snarkVM circuit/types/boolean/src/helpers/subtractor.rs
;   c0   = a xor b
;   diff = c0 xor borrow
;   c1   = (not a) and b          ; not is a linear combination, not a constraint
;   c2   = borrow and (not c0)
;   borrow_out = c1 or c2
;
; The xor/and/or constraints are the variable-variable gadgets already
; verified in r1cs/boolean-{xor,and,or}.  Negations use
; r1cs/boolean-and-notleft and boolean-and-notright, whose @('one')
; argument is snarkVM's public one variable.

(in-package "ALEOVM")

(include-book "../fun-specs/primitives-boolean")
(include-book "../r1cs/boolean-xor")
(include-book "../r1cs/boolean-and")
(include-book "../r1cs/boolean-or")
(include-book "../r1cs/boolean-and-notleft")
(include-book "../r1cs/boolean-and-notright")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-adder-gadget ((a symbolp)
                              (b symbolp)
                              (carry symbolp)
                              (c0 symbolp)
                              (sum symbolp)
                              (c1 symbolp)
                              (c2 symbolp)
                              (carry-out symbolp)
                              (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Boolean::adder') in the all-variable case."
  (append (boolean-xor-gadget a b c0 p)
          (boolean-xor-gadget c0 carry sum p)
          (boolean-and-gadget a b c1)
          (boolean-and-gadget carry c0 c2)
          (boolean-or-gadget c1 c2 carry-out p)))

(defruled boolean-adder-gadget-holdp-split
  (implies (and (symbolp a) (symbolp b) (symbolp carry)
                (symbolp c0) (symbolp sum)
                (symbolp c1) (symbolp c2) (symbolp carry-out)
                (primep p))
           (equal (r1cs::r1cs-constraints-holdp
                   (boolean-adder-gadget a b carry c0 sum c1 c2 carry-out p)
                   asg p)
                  (and (r1cs::r1cs-constraints-holdp
                        (boolean-xor-gadget a b c0 p) asg p)
                       (r1cs::r1cs-constraints-holdp
                        (boolean-xor-gadget c0 carry sum p) asg p)
                       (r1cs::r1cs-constraints-holdp
                        (boolean-and-gadget a b c1) asg p)
                       (r1cs::r1cs-constraints-holdp
                        (boolean-and-gadget carry c0 c2) asg p)
                       (r1cs::r1cs-constraints-holdp
                        (boolean-or-gadget c1 c2 carry-out p) asg p))))
  :enable boolean-adder-gadget)

(defruled boolean-xor-funspec-is-bitxor
  (implies (and (bitp x) (bitp y))
           (equal (boolean-xor-funspec x y) (bitxor x y)))
  :enable (boolean-xor-funspec bitxor))

(defruled boolean-and-funspec-is-bitand
  (implies (and (bitp x) (bitp y))
           (equal (boolean-and-funspec x y) (bitand x y)))
  :enable (boolean-and-funspec bitand))

(defruled boolean-or-funspec-is-bitor
  (implies (and (bitp x) (bitp y))
           (equal (boolean-or-funspec x y) (bitor x y)))
  :enable (boolean-or-funspec bitor))

(defruled boolean-adder-c0-when-hold
  (implies (and (symbolp a) (symbolp b) (symbolp c0)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c0)
                (bitp (lookup-equal a asg))
                (bitp (lookup-equal b asg))
                (r1cs::r1cs-constraints-holdp
                 (boolean-xor-gadget a b c0 p) asg p))
           (and (equal (lookup-equal c0 asg)
                       (boolean-xor-funspec (lookup-equal a asg)
                                            (lookup-equal b asg)))
                (bitp (lookup-equal c0 asg))))
  :enable boolean-xor-funspec-is-bitxor
  :use ((:instance boolean-xor-gadget-to-bitxor (x a) (y b) (z c0))))

(defruled boolean-adder-sum-when-hold
  (implies (and (symbolp c0) (symbolp carry) (symbolp sum)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c0)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg sum)
                (bitp (lookup-equal c0 asg))
                (bitp (lookup-equal carry asg))
                (r1cs::r1cs-constraints-holdp
                 (boolean-xor-gadget c0 carry sum p) asg p))
           (equal (lookup-equal sum asg)
                  (boolean-xor-funspec (lookup-equal c0 asg)
                                       (lookup-equal carry asg))))
  :enable boolean-xor-funspec-is-bitxor
  :use ((:instance boolean-xor-gadget-to-bitxor
                   (x c0) (y carry) (z sum))))

(defruled boolean-adder-c1-when-hold
  (implies (and (symbolp a) (symbolp b) (symbolp c1)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c1)
                (bitp (lookup-equal a asg))
                (bitp (lookup-equal b asg))
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-gadget a b c1) asg p))
           (and (equal (lookup-equal c1 asg)
                       (boolean-and-funspec (lookup-equal a asg)
                                            (lookup-equal b asg)))
                (bitp (lookup-equal c1 asg))))
  :enable boolean-and-funspec-is-bitand
  :use ((:instance boolean-and-gadget-to-bitand (x a) (y b) (z c1))))

(defruled boolean-adder-c2-when-hold
  (implies (and (symbolp carry) (symbolp c0) (symbolp c2)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg c0)
                (r1cs::valuation-bindsp asg c2)
                (bitp (lookup-equal carry asg))
                (bitp (lookup-equal c0 asg))
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-gadget carry c0 c2) asg p))
           (and (equal (lookup-equal c2 asg)
                       (boolean-and-funspec (lookup-equal carry asg)
                                            (lookup-equal c0 asg)))
                (bitp (lookup-equal c2 asg))))
  :enable boolean-and-funspec-is-bitand
  :use ((:instance boolean-and-gadget-to-bitand
                   (x carry) (y c0) (z c2))))

(defruled boolean-adder-cout-when-hold
  (implies (and (symbolp c1) (symbolp c2) (symbolp carry-out)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg c1)
                (r1cs::valuation-bindsp asg c2)
                (r1cs::valuation-bindsp asg carry-out)
                (bitp (lookup-equal c1 asg))
                (bitp (lookup-equal c2 asg))
                (r1cs::r1cs-constraints-holdp
                 (boolean-or-gadget c1 c2 carry-out p) asg p))
           (equal (lookup-equal carry-out asg)
                  (boolean-or-funspec (lookup-equal c1 asg)
                                      (lookup-equal c2 asg))))
  :enable boolean-or-funspec-is-bitor
  :use ((:instance boolean-or-gadget-to-bitor
                   (x c1) (y c2) (z carry-out))))

(defruled boolean-adder-gadget-sound
  :short "R1CS-SOUND for @('Boolean::adder')."
  (implies (and (symbolp a) (symbolp b) (symbolp carry)
                (symbolp c0) (symbolp sum)
                (symbolp c1) (symbolp c2) (symbolp carry-out)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg c0)
                (r1cs::valuation-bindsp asg sum)
                (r1cs::valuation-bindsp asg c1)
                (r1cs::valuation-bindsp asg c2)
                (r1cs::valuation-bindsp asg carry-out)
                (bitp (lookup-equal a asg))
                (bitp (lookup-equal b asg))
                (bitp (lookup-equal carry asg))
                (r1cs::r1cs-constraints-holdp
                 (boolean-adder-gadget a b carry c0 sum c1 c2 carry-out p)
                 asg p))
           (b* ((a$ (lookup-equal a asg))
                (b$ (lookup-equal b asg))
                (carry$ (lookup-equal carry asg))
                (sum$ (lookup-equal sum asg))
                (cout$ (lookup-equal carry-out asg))
                ((mv s co) (boolean-adder-funspec a$ b$ carry$)))
             (and (equal sum$ s)
                  (equal cout$ co))))
  :hints (("Goal"
           :in-theory (union-theories
                       '(boolean-adder-gadget-holdp-split
                         boolean-adder-funspec)
                       (theory 'minimal-theory))
           :use (boolean-adder-c0-when-hold
                 boolean-adder-sum-when-hold
                 boolean-adder-c1-when-hold
                 boolean-adder-c2-when-hold
                 boolean-adder-cout-when-hold))))

(defruled boolean-adder-gadget-complete
  :short "R1CS-COMPLETE for @('Boolean::adder').
          The witness wires are the intermediate bits of the funspec."
  (implies (and (symbolp a) (symbolp b) (symbolp carry)
                (symbolp c0) (symbolp sum)
                (symbolp c1) (symbolp c2) (symbolp carry-out)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg carry)
                (r1cs::valuation-bindsp asg c0)
                (r1cs::valuation-bindsp asg sum)
                (r1cs::valuation-bindsp asg c1)
                (r1cs::valuation-bindsp asg c2)
                (r1cs::valuation-bindsp asg carry-out)
                (bitp (lookup-equal a asg))
                (bitp (lookup-equal b asg))
                (bitp (lookup-equal carry asg))
                (bitp (lookup-equal c0 asg))
                (bitp (lookup-equal sum asg))
                (bitp (lookup-equal c1 asg))
                (bitp (lookup-equal c2 asg))
                (bitp (lookup-equal carry-out asg))
                (equal (lookup-equal c0 asg)
                       (boolean-xor-funspec (lookup-equal a asg)
                                            (lookup-equal b asg)))
                (equal (lookup-equal sum asg)
                       (boolean-xor-funspec (lookup-equal c0 asg)
                                            (lookup-equal carry asg)))
                (equal (lookup-equal c1 asg)
                       (boolean-and-funspec (lookup-equal a asg)
                                            (lookup-equal b asg)))
                (equal (lookup-equal c2 asg)
                       (boolean-and-funspec (lookup-equal carry asg)
                                            (lookup-equal c0 asg)))
                (equal (lookup-equal carry-out asg)
                       (boolean-or-funspec (lookup-equal c1 asg)
                                           (lookup-equal c2 asg))))
           (r1cs::r1cs-constraints-holdp
            (boolean-adder-gadget a b carry c0 sum c1 c2 carry-out p)
            asg p))
  :hints (("Goal"
           :in-theory (union-theories
                       '(boolean-adder-gadget-holdp-split
                         boolean-xor-funspec-is-bitxor
                         boolean-and-funspec-is-bitand
                         boolean-or-funspec-is-bitor
                         boolean-xor-gadget-to-bitxor
                         boolean-and-gadget-to-bitand
                         boolean-or-gadget-to-bitor
                         bitp-of-boolean-xor-funspec
                         bitp-of-boolean-and-funspec
                         bitp-of-boolean-or-funspec
                         bitp-of-bitxor
                         bitp-of-bitand
                         bitp-of-bitor)
                       (theory 'minimal-theory)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define boolean-subtractor-gadget ((a symbolp)
                                   (b symbolp)
                                   (borrow symbolp)
                                   (c0 symbolp)
                                   (difference symbolp)
                                   (c1 symbolp)
                                   (c2 symbolp)
                                   (borrow-out symbolp)
                                   (one symbolp)
                                   (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Boolean::subtractor') in the all-variable case."
  (append (boolean-xor-gadget a b c0 p)
          (boolean-xor-gadget c0 borrow difference p)
          (boolean-and-notleft-gadget a b c1 one p)
          (boolean-and-notright-gadget borrow c0 c2 one p)
          (boolean-or-gadget c1 c2 borrow-out p)))

(defruled boolean-subtractor-gadget-holdp-split
  (implies (and (symbolp a) (symbolp b) (symbolp borrow)
                (symbolp c0) (symbolp difference)
                (symbolp c1) (symbolp c2) (symbolp borrow-out)
                (symbolp one)
                (primep p))
           (equal (r1cs::r1cs-constraints-holdp
                   (boolean-subtractor-gadget
                    a b borrow c0 difference c1 c2 borrow-out one p)
                   asg p)
                  (and (r1cs::r1cs-constraints-holdp
                        (boolean-xor-gadget a b c0 p) asg p)
                       (r1cs::r1cs-constraints-holdp
                        (boolean-xor-gadget c0 borrow difference p) asg p)
                       (r1cs::r1cs-constraints-holdp
                        (boolean-and-notleft-gadget a b c1 one p) asg p)
                       (r1cs::r1cs-constraints-holdp
                        (boolean-and-notright-gadget borrow c0 c2 one p) asg p)
                       (r1cs::r1cs-constraints-holdp
                        (boolean-or-gadget c1 c2 borrow-out p) asg p))))
  :enable boolean-subtractor-gadget)

(defruled boolean-not-and-is-notleft
  (implies (and (bitp x) (bitp y))
           (equal (boolean-and-funspec (boolean-not-funspec x) y)
                  (if (and (equal x 0) (equal y 1)) 1 0)))
  :enable (boolean-and-funspec boolean-not-funspec))

(defruled boolean-and-not-is-notright
  (implies (and (bitp x) (bitp y))
           (equal (boolean-and-funspec x (boolean-not-funspec y))
                  (if (and (equal x 1) (equal y 0)) 1 0)))
  :enable (boolean-and-funspec boolean-not-funspec))

(defruled boolean-subtractor-c1-when-hold
  (implies (and (symbolp a) (symbolp b) (symbolp c1) (symbolp one)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg c1)
                (r1cs::valuation-bindsp asg one)
                (bitp (lookup-equal a asg))
                (bitp (lookup-equal b asg))
                (equal (lookup-equal one asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notleft-gadget a b c1 one p) asg p))
           (and (equal (lookup-equal c1 asg)
                       (boolean-and-funspec
                        (boolean-not-funspec (lookup-equal a asg))
                        (lookup-equal b asg)))
                (bitp (lookup-equal c1 asg))))
  :enable boolean-not-and-is-notleft
  :use ((:instance boolean-and-notleft-gadget-to-booland-boolnot
                   (x a) (y b) (z c1))))

(defruled boolean-subtractor-c2-when-hold
  (implies (and (symbolp borrow) (symbolp c0) (symbolp c2) (symbolp one)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg borrow)
                (r1cs::valuation-bindsp asg c0)
                (r1cs::valuation-bindsp asg c2)
                (r1cs::valuation-bindsp asg one)
                (bitp (lookup-equal borrow asg))
                (bitp (lookup-equal c0 asg))
                (equal (lookup-equal one asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (boolean-and-notright-gadget borrow c0 c2 one p) asg p))
           (and (equal (lookup-equal c2 asg)
                       (boolean-and-funspec
                        (lookup-equal borrow asg)
                        (boolean-not-funspec (lookup-equal c0 asg))))
                (bitp (lookup-equal c2 asg))))
  :enable boolean-and-not-is-notright
  :use ((:instance boolean-and-notright-gadget-to-booland-boolnot
                   (x borrow) (y c0) (z c2))))

(defruled boolean-subtractor-gadget-sound
  :short "R1CS-SOUND for @('Boolean::subtractor')."
  (implies (and (symbolp a) (symbolp b) (symbolp borrow)
                (symbolp c0) (symbolp difference)
                (symbolp c1) (symbolp c2) (symbolp borrow-out)
                (symbolp one)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg borrow)
                (r1cs::valuation-bindsp asg c0)
                (r1cs::valuation-bindsp asg difference)
                (r1cs::valuation-bindsp asg c1)
                (r1cs::valuation-bindsp asg c2)
                (r1cs::valuation-bindsp asg borrow-out)
                (r1cs::valuation-bindsp asg one)
                (bitp (lookup-equal a asg))
                (bitp (lookup-equal b asg))
                (bitp (lookup-equal borrow asg))
                (equal (lookup-equal one asg) 1)
                (r1cs::r1cs-constraints-holdp
                 (boolean-subtractor-gadget
                  a b borrow c0 difference c1 c2 borrow-out one p)
                 asg p))
           (b* ((a$ (lookup-equal a asg))
                (b$ (lookup-equal b asg))
                (borrow$ (lookup-equal borrow asg))
                (diff$ (lookup-equal difference asg))
                (bout$ (lookup-equal borrow-out asg))
                ((mv d bo) (boolean-subtractor-funspec a$ b$ borrow$)))
             (and (equal diff$ d)
                  (equal bout$ bo))))
  :hints (("Goal"
           :in-theory (union-theories
                       '(boolean-subtractor-gadget-holdp-split
                         boolean-subtractor-funspec)
                       (theory 'minimal-theory))
           :use (boolean-adder-c0-when-hold
                 (:instance boolean-adder-sum-when-hold
                            (carry borrow)
                            (sum difference))
                 boolean-subtractor-c1-when-hold
                 boolean-subtractor-c2-when-hold
                 (:instance boolean-adder-cout-when-hold
                            (carry-out borrow-out))))))

(defruled boolean-subtractor-gadget-complete
  :short "R1CS-COMPLETE for @('Boolean::subtractor')."
  (implies (and (symbolp a) (symbolp b) (symbolp borrow)
                (symbolp c0) (symbolp difference)
                (symbolp c1) (symbolp c2) (symbolp borrow-out)
                (symbolp one)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg a)
                (r1cs::valuation-bindsp asg b)
                (r1cs::valuation-bindsp asg borrow)
                (r1cs::valuation-bindsp asg c0)
                (r1cs::valuation-bindsp asg difference)
                (r1cs::valuation-bindsp asg c1)
                (r1cs::valuation-bindsp asg c2)
                (r1cs::valuation-bindsp asg borrow-out)
                (r1cs::valuation-bindsp asg one)
                (bitp (lookup-equal a asg))
                (bitp (lookup-equal b asg))
                (bitp (lookup-equal borrow asg))
                (bitp (lookup-equal c0 asg))
                (bitp (lookup-equal difference asg))
                (bitp (lookup-equal c1 asg))
                (bitp (lookup-equal c2 asg))
                (bitp (lookup-equal borrow-out asg))
                (equal (lookup-equal one asg) 1)
                (equal (lookup-equal c0 asg)
                       (boolean-xor-funspec (lookup-equal a asg)
                                            (lookup-equal b asg)))
                (equal (lookup-equal difference asg)
                       (boolean-xor-funspec (lookup-equal c0 asg)
                                            (lookup-equal borrow asg)))
                (equal (lookup-equal c1 asg)
                       (boolean-and-funspec
                        (boolean-not-funspec (lookup-equal a asg))
                        (lookup-equal b asg)))
                (equal (lookup-equal c2 asg)
                       (boolean-and-funspec
                        (lookup-equal borrow asg)
                        (boolean-not-funspec (lookup-equal c0 asg))))
                (equal (lookup-equal borrow-out asg)
                       (boolean-or-funspec (lookup-equal c1 asg)
                                           (lookup-equal c2 asg))))
           (r1cs::r1cs-constraints-holdp
            (boolean-subtractor-gadget
             a b borrow c0 difference c1 c2 borrow-out one p)
            asg p))
  :hints (("Goal"
           :in-theory (union-theories
                       '(boolean-subtractor-gadget-holdp-split
                         boolean-xor-funspec-is-bitxor
                         boolean-not-and-is-notleft
                         boolean-and-not-is-notright
                         boolean-or-funspec-is-bitor
                         boolean-xor-gadget-to-bitxor
                         boolean-and-notleft-gadget-to-booland-boolnot
                         boolean-and-notright-gadget-to-booland-boolnot
                         boolean-or-gadget-to-bitor
                         bitp-of-boolean-xor-funspec
                         bitp-of-boolean-and-funspec
                         bitp-of-boolean-or-funspec
                         bitp-of-boolean-not-funspec
                         bitp-of-bitxor
                         bitp-of-bitand
                         bitp-of-bitor)
                       (theory 'minimal-theory)))))
