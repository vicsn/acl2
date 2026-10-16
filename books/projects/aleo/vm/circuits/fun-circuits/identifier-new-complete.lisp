; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; R1CS-COMPLETE for snarkVM IdentifierLiteral::new, the identifier arm of
; Literal::new.  The constraints are identifier-new-gadget
; (identifier-new-r1cs.lisp); soundness is identifier-list-sound.lisp.
;
; Every wire of validate_byte is a function of the byte's 8 bits.
; id-byte-wits is that function, in the witness layout of id-byte-gadget.
; The is_not_equal witness m is the inverse of the low-5-bit sum, and 0 when
; that sum is 0.  id-first-wits is the underscore and letter wires of the
; first byte.  id-byte-ok-upto evaluates, for all 256 bytes, that the byte
; equations and the first-byte equations hold whenever validate-byte accepts
; the byte, and that the null wire is the flag validate-byte returns.  The
; trailing-null constraints hold because validate-trailing-nulls accepts
; those flags.

(in-package "ALEOVM")

(include-book "identifier-list-sound")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))

(local (in-theory (disable (:e base-prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define id-byte-wits ((bits bit-listp))
  :verify-guards nil
  :returns (wits true-listp)
  :short "The 12 validate_byte wires of a byte, in the order of
          @(tsee id-byte-gadget)."
  (b* ((p (base-prime))
       (b0 (bfix (nth 0 bits))) (b1 (bfix (nth 1 bits)))
       (b2 (bfix (nth 2 bits))) (b3 (bfix (nth 3 bits)))
       (b4 (bfix (nth 4 bits))) (b5 (bfix (nth 5 bits)))
       (b6 (bfix (nth 6 bits)))
       (s (+ b0 b1 b2 b3 b4))
       (b4b3 (bitand b4 b3))
       (b1b0 (bitand b1 b0))
       (m (if (equal s 0) 0 (pfield::inv s p)))
       (r (if (equal s 0) 0 1))
       (null (values-b-and (values-b-not b6) (values-b-not b5)))
       (lower (bitand b6 b5))
       (dor (bitor b2 b1))
       (idig (bitand b3 dor))
       (xor (bitxor b2 b1b0))
       (bu (bitand b4b3 xor))
       (lor (bitor b2 b1b0))
       (bl (bitand b4b3 lor)))
    (list b4b3 b1b0 m r null lower dor idig xor bu lor bl))
  ///
  (defret len-of-id-byte-wits
    (equal (len wits) 12))
  (defret id-byte-wits-bitps
    (and (bitp (nth 0 wits))
         (bitp (nth 1 wits))
         (bitp (nth 4 wits))
         (bitp (nth 6 wits))
         (bitp (nth 8 wits))
         (bitp (nth 10 wits)))
    :hints (("Goal" :in-theory (enable bitp-of-values-b-and)))))

(define id-first-wits ((bits bit-listp))
  :verify-guards nil
  :returns (wits true-listp)
  :short "The partial-underscore, underscore and letter wires of the first
          byte, in the order of @(tsee id-first-extra-gadget)."
  (b* ((p (base-prime))
       (b0 (bfix (nth 0 bits))) (b1 (bfix (nth 1 bits)))
       (b2 (bfix (nth 2 bits))) (b3 (bfix (nth 3 bits)))
       (b4 (bfix (nth 4 bits))) (b6 (bfix (nth 6 bits)))
       (partial (bitand (bitand b4 b3) (bitand b1 b0)))
       (uscore (bitand partial b2))
       (islet (pfield::mul b6 (pfield::sub 1 uscore p) p)))
    (list partial uscore islet))
  ///
  (defret id-first-wits-bitp
    (bitp (nth 0 wits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The per-byte check, evaluated for all 256 bytes.

(define id-byte-ok ((v natp) (firstp booleanp))
  :verify-guards nil
  (b* ((p (base-prime))
       (bits (values-nat-to-lebits 8 v))
       (w (id-byte-wits bits))
       (f (id-first-wits bits)))
    (or (reserrp (validate-byte bits firstp))
        (and (id-byte-equations (nth 0 bits) (nth 1 bits)
                                (nth 2 bits) (nth 3 bits)
                                (nth 4 bits) (nth 5 bits)
                                (nth 6 bits) (nth 7 bits)
                                (nth 0 w) (nth 1 w) (nth 2 w) (nth 3 w)
                                (nth 4 w) (nth 5 w) (nth 6 w) (nth 7 w)
                                (nth 8 w) (nth 9 w) (nth 10 w) (nth 11 w)
                                p)
             (equal (nth 4 w) (validate-byte bits firstp))
             (or (not firstp)
                 (id-first-extra-equations (nth 0 w) (nth 1 w)
                                           (nth 2 bits) (nth 6 bits)
                                           (nth 0 f) (nth 1 f) (nth 2 f)
                                           p))))))

(define id-byte-ok-upto ((n natp))
  :verify-guards nil
  (and (id-byte-ok n t)
       (id-byte-ok n nil)
       (if (zp n)
           t
         (id-byte-ok-upto (1- n)))))

(defruled id-byte-ok-upto-255
  (id-byte-ok-upto 255)
  :in-theory '((:e id-byte-ok-upto)))

(defruled id-byte-ok-when-upto
  (implies (and (id-byte-ok-upto n)
                (natp n)
                (natp v)
                (<= v n))
           (and (id-byte-ok v t)
                (id-byte-ok v nil)))
  :induct (id-byte-ok-upto n)
  :enable id-byte-ok-upto
  :disable id-byte-ok)

(defruled id-byte-ok-of-ubyte8
  (implies (acl2::ubyte8p v)
           (and (id-byte-ok v t)
                (id-byte-ok v nil)))
  :use (id-byte-ok-upto-255
        (:instance id-byte-ok-when-upto (n 255)))
  :enable acl2::ubyte8p
  :disable id-byte-ok)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; One byte, over the wires.

(defruled id-byte-gadget-complete
  (implies (and (symbol-listp bits) (equal (len bits) 8)
                (symbol-listp wits) (equal (len wits) 12)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg wits)
                (acl2::ubyte8p v)
                (booleanp firstp)
                (equal (lookup-equal-list bits asg)
                       (values-nat-to-lebits 8 v))
                (equal (lookup-equal-list wits asg)
                       (id-byte-wits (values-nat-to-lebits 8 v)))
                (not (reserrp (validate-byte (values-nat-to-lebits 8 v)
                                             firstp))))
           (and (r1cs::r1cs-constraints-holdp
                 (id-byte-gadget bits wits p) asg p)
                (equal (lookup-equal (nth 4 wits) asg)
                       (validate-byte (values-nat-to-lebits 8 v) firstp))))
  :do-not-induct t
  :cases ((equal firstp t))
  :use ((:instance id-byte-gadget-to-equations)
        (:instance id-byte-ok-of-ubyte8))
  :enable id-byte-ok
  :disable (id-byte-gadget-to-equations
            id-byte-ok-of-ubyte8
            id-byte-wits
            id-first-wits
            values-nat-to-lebits
            validate-byte
            id-byte-equations
            id-first-extra-equations
            id-byte-gadget
            (:definition nth)))

(defruled id-first-extra-gadget-complete
  (implies (and (symbol-listp bits) (equal (len bits) 8)
                (symbol-listp wits) (equal (len wits) 12)
                (symbolp partial) (symbolp uscore) (symbolp islet)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg bits)
                (r1cs::valuation-binds-allp asg wits)
                (r1cs::valuation-bindsp asg partial)
                (r1cs::valuation-bindsp asg uscore)
                (r1cs::valuation-bindsp asg islet)
                (acl2::ubyte8p v)
                (equal (lookup-equal-list bits asg)
                       (values-nat-to-lebits 8 v))
                (equal (lookup-equal-list wits asg)
                       (id-byte-wits (values-nat-to-lebits 8 v)))
                (equal (lookup-equal partial asg)
                       (nth 0 (id-first-wits (values-nat-to-lebits 8 v))))
                (equal (lookup-equal uscore asg)
                       (nth 1 (id-first-wits (values-nat-to-lebits 8 v))))
                (equal (lookup-equal islet asg)
                       (nth 2 (id-first-wits (values-nat-to-lebits 8 v))))
                (not (reserrp (validate-byte (values-nat-to-lebits 8 v) t))))
           (r1cs::r1cs-constraints-holdp
            (id-first-extra-gadget (nth 0 wits) (nth 1 wits)
                                   (nth 2 bits) (nth 6 bits)
                                   partial uscore islet p)
            asg p))
  :do-not-induct t
  :use ((:instance id-first-extra-gadget-to-equations
                   (b4b3 (nth 0 wits)) (b1b0 (nth 1 wits))
                   (b2 (nth 2 bits)) (b6 (nth 6 bits)))
        (:instance id-byte-ok-of-ubyte8)
        (:instance id-first-wits-bitp (bits (values-nat-to-lebits 8 v))))
  :enable id-byte-ok
  :disable (id-first-extra-gadget-to-equations
            id-byte-ok-of-ubyte8
            id-first-wits-bitp
            id-byte-wits
            id-first-wits
            values-nat-to-lebits
            validate-byte
            id-byte-equations
            id-first-extra-equations
            id-first-extra-gadget
            (:definition nth)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The rows.

(define id-wits-matchp ((bytes acl2::ubyte8-listp)
                        (witrows true-listp)
                        (asg alistp))
  :verify-guards nil
  :returns (yes/no booleanp)
  :short "Each witness row holds @(tsee id-byte-wits) of its byte."
  (if (atom bytes)
      (atom witrows)
    (and (consp witrows)
         (equal (lookup-equal-list (car witrows) asg)
                (id-byte-wits
                 (values-nat-to-lebits 8 (acl2::ubyte8-fix (car bytes)))))
         (id-wits-matchp (cdr bytes) (cdr witrows) asg))))

(defruled id-bit-checks-complete
  (implies (and (id-bitrows-p bitrows)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (id-bitrows-all-boundp bitrows asg)
                (id-bits-matchp bytes bitrows asg))
           (r1cs::r1cs-constraints-holdp
            (id-bit-checks bitrows p) asg p))
  :induct (id-bits-matchp bytes bitrows asg)
  :enable (id-bit-checks
           id-bits-matchp
           id-bitrows-all-boundp
           id-bitrows-p
           boolean-check-gadget-list-to-bit-listp
           r1cs::r1cs-constraints-holdp-of-append)
  :disable lookup-equal-of-nth)

(defruled id-rest-bytes-gadget-complete
  (implies (and (id-bitrows-p bitrows)
                (id-witrows-p witrows)
                (acl2::ubyte8-listp bytes)
                (equal (len bitrows) (len bytes))
                (equal (len witrows) (len bitrows))
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (id-rows-boundp bitrows witrows asg)
                (id-bits-matchp bytes bitrows asg)
                (id-wits-matchp bytes witrows asg)
                (not (reserrp (values-validate-bytes-null-flags bytes nil))))
           (and (r1cs::r1cs-constraints-holdp
                 (id-rest-bytes-gadget bitrows witrows p) asg p)
                (equal (id-lookup-nulls witrows asg)
                       (values-validate-bytes-null-flags bytes nil))))
  :induct (id-rest-induct bytes bitrows witrows)
  :hints (("Goal"
           :in-theory (e/d (id-rest-bytes-gadget
                            id-rest-induct
                            values-validate-bytes-null-flags
                            id-lookup-nulls
                            id-bits-matchp
                            id-wits-matchp
                            id-rows-boundp
                            id-bitrows-p
                            id-witrows-p
                            len
                            acl2::ubyte8-listp
                            acl2::ubyte8-fix
                            r1cs::r1cs-constraints-holdp-of-append)
                           (validate-byte
                            id-byte-wits
                            values-nat-to-lebits
                            lookup-equal-of-nth
                            (:definition id-byte-gadget))))
          ("Subgoal *1/2"
           :do-not-induct t
           :use ((:instance id-byte-gadget-complete
                            (bits (car bitrows))
                            (wits (car witrows))
                            (v (car bytes))
                            (firstp nil))))))

(defruled id-trailing-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp nulls)
                (r1cs::valuation-binds-allp asg nulls)
                (bit-listp (lookup-equal-list nulls asg))
                (equal (validate-trailing-nulls (lookup-equal-list nulls asg))
                       t))
           (r1cs::r1cs-constraints-holdp
            (id-trailing-gadget nulls p) asg p))
  :hints (("Goal"
           :induct (id-trailing-gadget nulls p)
           :in-theory (e/d (id-trailing-gadget
                            validate-trailing-nulls
                            id-trail-gadget-to-mul
                            id-sub1-of-bit
                            id-mul-of-bits
                            bitp-of-values-b-not
                            lookup-equal-list
                            bit-listp
                            symbol-listp
                            acl2::bfix-when-bitp
                            (:definition r1cs::valuation-binds-allp)
                            r1cs::r1cs-constraints-holdp-of-append
                            primep-when-equal-base-prime)
                           ((:definition id-trail-gadget)
                            (:definition pfield::mul)
                            (:definition pfield::sub)
                            lookup-equal-of-nth)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled id-new-gadget-split
  (equal (r1cs::r1cs-constraints-holdp
          (identifier-new-gadget bitrows witrows partial uscore islet p)
          asg p)
         (and (r1cs::r1cs-constraints-holdp
               (id-bit-checks bitrows p) asg p)
              (r1cs::r1cs-constraints-holdp
               (id-byte-gadget (car bitrows) (car witrows) p) asg p)
              (r1cs::r1cs-constraints-holdp
               (id-first-extra-gadget (nth 0 (car witrows))
                                      (nth 1 (car witrows))
                                      (nth 2 (car bitrows))
                                      (nth 6 (car bitrows))
                                      partial uscore islet p)
               asg p)
              (r1cs::r1cs-constraints-holdp
               (id-rest-bytes-gadget (cdr bitrows) (cdr witrows) p) asg p)
              (r1cs::r1cs-constraints-holdp
               (id-trailing-gadget (id-null-symbols witrows) p) asg p)))
  :in-theory '(identifier-new-gadget
               r1cs::r1cs-constraints-holdp-of-append))

(defruled id-rows-car-facts
  (implies (and (consp bytes)
                (acl2::ubyte8-listp bytes)
                (id-bitrows-p bitrows)
                (id-witrows-p witrows)
                (equal (len bitrows) (len bytes))
                (equal (len witrows) (len bitrows))
                (id-rows-boundp bitrows witrows asg)
                (id-bits-matchp bytes bitrows asg)
                (id-wits-matchp bytes witrows asg))
           (and (acl2::ubyte8p (car bytes))
                (acl2::ubyte8-listp (cdr bytes))
                (symbol-listp (car bitrows))
                (equal (len (car bitrows)) 8)
                (symbol-listp (car witrows))
                (equal (len (car witrows)) 12)
                (id-bitrows-p (cdr bitrows))
                (id-witrows-p (cdr witrows))
                (equal (len (cdr bitrows)) (len (cdr bytes)))
                (equal (len (cdr witrows)) (len (cdr bitrows)))
                (r1cs::valuation-binds-allp asg (car bitrows))
                (r1cs::valuation-binds-allp asg (car witrows))
                (id-rows-boundp (cdr bitrows) (cdr witrows) asg)
                (id-bits-matchp (cdr bytes) (cdr bitrows) asg)
                (id-wits-matchp (cdr bytes) (cdr witrows) asg)
                (equal (lookup-equal-list (car bitrows) asg)
                       (values-nat-to-lebits 8 (car bytes)))
                (equal (lookup-equal-list (car witrows) asg)
                       (id-byte-wits (values-nat-to-lebits 8 (car bytes))))))
  :do-not-induct t
  :enable (id-bits-matchp
           id-wits-matchp
           id-rows-boundp
           id-bitrows-p
           id-witrows-p
           acl2::ubyte8-listp
           acl2::ubyte8-fix
           len)
  :disable (id-byte-wits
            values-nat-to-lebits
            lookup-equal-of-nth))

(defruled id-validate-identifier-bytes-facts
  (implies (and (consp bytes)
                (acl2::ubyte8-listp bytes)
                (equal (validate-identifier-bytes bytes) t))
           (b* ((flag (validate-byte (values-nat-to-lebits 8 (car bytes)) t))
                (flags (values-validate-bytes-null-flags (cdr bytes) nil)))
             (and (not (reserrp flag))
                  (not (reserrp flags))
                  (bit-listp (cons flag flags))
                  (equal (validate-trailing-nulls (cons flag flags)) t))))
  :do-not-induct t
  :enable (validate-identifier-bytes
           values-validate-bytes-null-flags
           acl2::ubyte8-listp
           acl2::ubyte8-fix)
  :disable (validate-byte
            validate-trailing-nulls
            values-nat-to-lebits))

(defruled id-lookup-null-symbols-of-cons
  (implies (and (id-witrows-p witrows)
                (consp witrows))
           (equal (lookup-equal-list (id-null-symbols witrows) asg)
                  (cons (lookup-equal (nth 4 (car witrows)) asg)
                        (id-lookup-nulls (cdr witrows) asg))))
  :use id-null-symbols-lookup
  :enable id-lookup-nulls)

(defmacro id-new-hyps ()
  '(and (acl2::ubyte8-listp bytes)
        (consp bytes)
        (equal (validate-identifier-bytes bytes) t)
        (id-bitrows-p bitrows)
        (id-witrows-p witrows)
        (equal (len bitrows) (len bytes))
        (equal (len witrows) (len bitrows))
        (symbolp partial) (symbolp uscore) (symbolp islet)
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg partial)
        (r1cs::valuation-bindsp asg uscore)
        (r1cs::valuation-bindsp asg islet)
        (id-rows-boundp bitrows witrows asg)
        (id-bits-matchp bytes bitrows asg)
        (id-wits-matchp bytes witrows asg)
        (equal (lookup-equal partial asg)
               (nth 0 (id-first-wits (values-nat-to-lebits 8 (car bytes)))))
        (equal (lookup-equal uscore asg)
               (nth 1 (id-first-wits (values-nat-to-lebits 8 (car bytes)))))
        (equal (lookup-equal islet asg)
               (nth 2 (id-first-wits (values-nat-to-lebits 8 (car bytes)))))))

(defruledl id-new-part-bit-checks
  (implies (id-new-hyps)
           (r1cs::r1cs-constraints-holdp (id-bit-checks bitrows p) asg p))
  :do-not-induct t
  :use (id-bitrows-bound-from-rows id-bit-checks-complete)
  :disable (id-byte-wits id-first-wits values-nat-to-lebits validate-byte
            validate-trailing-nulls values-validate-bytes-null-flags
            validate-identifier-bytes
            id-byte-gadget id-first-extra-gadget id-rest-bytes-gadget
            id-trailing-gadget id-bit-checks identifier-new-gadget
            id-bits-matchp id-wits-matchp id-rows-boundp id-bitrows-p id-witrows-p
            id-null-symbols id-lookup-nulls lookup-equal-of-nth
            (:definition nth)))

(defruledl id-new-part-first-byte
  (implies (id-new-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (id-byte-gadget (car bitrows) (car witrows) p) asg p)
                (equal (lookup-equal (nth 4 (car witrows)) asg)
                       (validate-byte (values-nat-to-lebits 8 (car bytes)) t))))
  :do-not-induct t
  :use (id-rows-car-facts
        id-validate-identifier-bytes-facts
        (:instance id-byte-gadget-complete
                   (bits (car bitrows))
                   (wits (car witrows))
                   (v (car bytes))
                   (firstp t)))
  :disable (id-byte-wits id-first-wits values-nat-to-lebits validate-byte
            validate-trailing-nulls values-validate-bytes-null-flags
            validate-identifier-bytes
            id-byte-gadget id-first-extra-gadget id-rest-bytes-gadget
            id-trailing-gadget id-bit-checks identifier-new-gadget
            id-bits-matchp id-wits-matchp id-rows-boundp id-bitrows-p id-witrows-p
            id-null-symbols id-lookup-nulls lookup-equal-of-nth
            (:definition nth)))

(defruledl id-new-part-first-extra
  (implies (id-new-hyps)
           (r1cs::r1cs-constraints-holdp
            (id-first-extra-gadget (nth 0 (car witrows))
                                   (nth 1 (car witrows))
                                   (nth 2 (car bitrows))
                                   (nth 6 (car bitrows))
                                   partial uscore islet p)
            asg p))
  :do-not-induct t
  :use (id-rows-car-facts
        id-validate-identifier-bytes-facts
        (:instance id-first-extra-gadget-complete
                   (bits (car bitrows))
                   (wits (car witrows))
                   (v (car bytes))))
  :disable (id-byte-wits id-first-wits values-nat-to-lebits validate-byte
            validate-trailing-nulls values-validate-bytes-null-flags
            validate-identifier-bytes
            id-byte-gadget id-first-extra-gadget id-rest-bytes-gadget
            id-trailing-gadget id-bit-checks identifier-new-gadget
            id-bits-matchp id-wits-matchp id-rows-boundp id-bitrows-p id-witrows-p
            id-null-symbols id-lookup-nulls lookup-equal-of-nth
            (:definition nth)))

(defruledl id-new-part-rest
  (implies (id-new-hyps)
           (and (r1cs::r1cs-constraints-holdp
                 (id-rest-bytes-gadget (cdr bitrows) (cdr witrows) p) asg p)
                (equal (id-lookup-nulls (cdr witrows) asg)
                       (values-validate-bytes-null-flags (cdr bytes) nil))))
  :do-not-induct t
  :use (id-rows-car-facts
        id-validate-identifier-bytes-facts
        (:instance id-rest-bytes-gadget-complete
                   (bytes (cdr bytes))
                   (bitrows (cdr bitrows))
                   (witrows (cdr witrows))))
  :disable (id-byte-wits id-first-wits values-nat-to-lebits validate-byte
            validate-trailing-nulls values-validate-bytes-null-flags
            validate-identifier-bytes
            id-byte-gadget id-first-extra-gadget id-rest-bytes-gadget
            id-trailing-gadget id-bit-checks identifier-new-gadget
            id-bits-matchp id-wits-matchp id-rows-boundp id-bitrows-p id-witrows-p
            id-null-symbols id-lookup-nulls lookup-equal-of-nth
            (:definition nth)))

(defruledl id-new-nulls-lookup
  (implies (id-new-hyps)
           (equal (lookup-equal-list (id-null-symbols witrows) asg)
                  (cons (validate-byte (values-nat-to-lebits 8 (car bytes)) t)
                        (values-validate-bytes-null-flags (cdr bytes) nil))))
  :do-not-induct t
  :use (id-rows-car-facts
        id-new-part-first-byte
        id-new-part-rest
        id-lookup-null-symbols-of-cons)
  :disable (id-byte-wits id-first-wits values-nat-to-lebits validate-byte
            validate-trailing-nulls values-validate-bytes-null-flags
            validate-identifier-bytes
            id-byte-gadget id-first-extra-gadget id-rest-bytes-gadget
            id-trailing-gadget id-bit-checks identifier-new-gadget
            id-bits-matchp id-wits-matchp id-rows-boundp id-bitrows-p id-witrows-p
            id-null-symbols id-lookup-nulls lookup-equal-of-nth
            (:definition nth)))

(defruledl id-new-part-trailing
  (implies (id-new-hyps)
           (r1cs::r1cs-constraints-holdp
            (id-trailing-gadget (id-null-symbols witrows) p) asg p))
  :do-not-induct t
  :use (id-validate-identifier-bytes-facts
        id-new-nulls-lookup
        (:instance id-null-symbols-boundp)
        (:instance id-trailing-gadget-complete
                   (nulls (id-null-symbols witrows))))
  :disable (id-byte-wits id-first-wits values-nat-to-lebits validate-byte
            validate-trailing-nulls values-validate-bytes-null-flags
            validate-identifier-bytes
            id-byte-gadget id-first-extra-gadget id-rest-bytes-gadget
            id-trailing-gadget id-bit-checks identifier-new-gadget
            id-bits-matchp id-wits-matchp id-rows-boundp id-bitrows-p id-witrows-p
            id-null-symbols id-lookup-nulls lookup-equal-of-nth
            (:definition nth)))

(defruled identifier-new-gadget-complete
  :short "R1CS-COMPLETE, success half, of @('IdentifierLiteral::new'): for
          bytes that validate, the bit rows of the bytes, the validate_byte
          wires of @(tsee id-byte-wits), and the first-byte wires of
          @(tsee id-first-wits) satisfy @(tsee identifier-new-gadget)."
  (implies (id-new-hyps)
           (r1cs::r1cs-constraints-holdp
            (identifier-new-gadget bitrows witrows partial uscore islet p)
            asg p))
  :do-not-induct t
  :use (id-new-gadget-split
        id-new-part-bit-checks
        id-new-part-first-byte
        id-new-part-first-extra
        id-new-part-rest
        id-new-part-trailing)
  :in-theory nil)

(defruledl id-validate-trailing-nulls-when-ok
  (implies (not (reserrp (validate-trailing-nulls flags)))
           (equal (validate-trailing-nulls flags) t))
  :use (:instance values-unit-resultp-of-validate-trailing-nulls
                  (null-flags flags))
  :enable values-unit-resultp
  :disable values-unit-resultp-of-validate-trailing-nulls)

(defruled literal-identifier-new-complete
  :short "R1CS-COMPLETE for the identifier arm of @('Literal::new'): an
          identifier literal that @('literal-new') accepts has a satisfying
          assignment, and @('literal-new') returns it unchanged.  An
          identifier that @('literal-new') rejects has none
          (@(tsee literal-identifier-new-sound-of-bytes))."
  (implies (and (literalp x)
                (literal-case x :identifier)
                (equal bytes (identifier-literal->bytes
                              (literal-identifier->get x)))
                (consp bytes)
                (not (reserrp (literal-new x)))
                (id-bitrows-p bitrows)
                (id-witrows-p witrows)
                (equal (len bitrows) (len bytes))
                (equal (len witrows) (len bitrows))
                (symbolp partial) (symbolp uscore) (symbolp islet)
                (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg partial)
                (r1cs::valuation-bindsp asg uscore)
                (r1cs::valuation-bindsp asg islet)
                (id-rows-boundp bitrows witrows asg)
                (id-bits-matchp bytes bitrows asg)
                (id-wits-matchp bytes witrows asg)
                (equal (lookup-equal partial asg)
                       (nth 0 (id-first-wits
                               (values-nat-to-lebits 8 (car bytes)))))
                (equal (lookup-equal uscore asg)
                       (nth 1 (id-first-wits
                               (values-nat-to-lebits 8 (car bytes)))))
                (equal (lookup-equal islet asg)
                       (nth 2 (id-first-wits
                               (values-nat-to-lebits 8 (car bytes))))))
           (and (r1cs::r1cs-constraints-holdp
                 (literal-identifier-new-gadget
                  bitrows witrows partial uscore islet p)
                 asg p)
                (equal (literal-new x) (literal-fix x))))
  :do-not-induct t
  :hints (("Goal"
           :use ((:instance identifier-new-gadget-complete)
                 (:instance id-validate-trailing-nulls-when-ok
                            (flags (values-validate-bytes-null-flags
                                    bytes t))))
           :in-theory (e/d (literal-new
                            literal-identifier-new-gadget
                            identifier-literal-new
                            validate-identifier-bytes)
                           (identifier-new-gadget-complete
                            identifier-new-gadget
                            values-validate-bytes-null-flags
                            validate-trailing-nulls)))))
