; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; IdentifierLiteral::from_bits_le, from_bits_be and from_field
; (circuit/types/string/src/identifier_literal/helpers/from_bits.rs,
; from_field.rs), with every constraint snarkVM emits.
;
; from_bits_le on at least 248 bits: Boolean::assert_bits_are_zero on the
; bits past 248 (idlit-from-bits-le-gadget), then U8::from_bits_le of
; each 8-bit chunk (no constraint; the byte bits are the input wires),
; then from_bytes, which is validate_identifier_bytes: validate_byte of
; each byte, the first-byte extra gate, and the trailing-null chain.  It
; boolean-checks nothing; the input bits are Booleans already.  The
; gadget is that list over the first 248 input wires (31 rows of 8) and
; the excess wires.  Fewer than 248 bits pads with constant false, which
; is a different constraint system and is not covered here.
; from_bits_be reverses the input and emits nothing further.
; from_field is Field::to_bits_le (field-to-bits-gadget, 253 bits)
; followed by from_bits_le of those 253 wires.

(in-package "ALEOVM")

(include-book "identifier-new-complete")
(include-book "identifier-list-sound")
(include-book "val-string-ops")
(include-book "fsa-identifier-literal-bits")
(include-book "fb2-field-bits")

(local (include-book "std/lists/top" :dir :system))

(local (in-theory (disable lookup-equal-of-nth)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fsa-idlit-validate-gadget ((bitrows true-listp)
                                   (witrows true-listp)
                                   (partial symbolp) (uscore symbolp)
                                   (islet symbolp)
                                   (p primep))
  :verify-guards nil
  :short "@('validate_identifier_bytes'): @(tsee identifier-new-gadget)
          without the boolean checks."
  (append (id-byte-gadget (car bitrows) (car witrows) p)
          (id-first-extra-gadget (nth 0 (car witrows))
                                 (nth 1 (car witrows))
                                 (nth 2 (car bitrows))
                                 (nth 6 (car bitrows))
                                 partial uscore islet p)
          (id-rest-bytes-gadget (cdr bitrows) (cdr witrows) p)
          (id-trailing-gadget (id-null-symbols witrows) p)))

(define fsa-idlit-from-bits-le-gadget ((bitrows true-listp)
                                       (excess symbol-listp)
                                       (witrows true-listp)
                                       (partial symbolp) (uscore symbolp)
                                       (islet symbolp)
                                       (p primep))
  :verify-guards nil
  (append (idlit-from-bits-le-gadget excess)
          (fsa-idlit-validate-gadget bitrows witrows partial uscore islet p)))

(define fsa-idlit-from-field-gadget ((x symbolp)
                                     (rs symbol-listp)
                                     (u symbolp)
                                     (bitrows true-listp)
                                     (excess symbol-listp)
                                     (witrows true-listp)
                                     (partial symbolp) (uscore symbolp)
                                     (islet symbolp)
                                     (p primep))
  :verify-guards nil
  (append (field-to-bits-gadget x (append (fsa-id-flatten bitrows) excess)
                                rs u p)
          (fsa-idlit-from-bits-le-gadget bitrows excess witrows
                                         partial uscore islet p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fsa-id-new-gadget-as-validate
  (equal (r1cs::r1cs-constraints-holdp
          (identifier-new-gadget bitrows witrows partial uscore islet p)
          asg p)
         (and (r1cs::r1cs-constraints-holdp (id-bit-checks bitrows p) asg p)
              (r1cs::r1cs-constraints-holdp
               (fsa-idlit-validate-gadget bitrows witrows
                                          partial uscore islet p)
               asg p)))
  :in-theory '(identifier-new-gadget
               fsa-idlit-validate-gadget
               r1cs::r1cs-constraints-holdp-of-append))

(defruledl fsa-lookup-list-append
  (equal (lookup-equal-list (append a b) asg)
         (append (lookup-equal-list a asg) (lookup-equal-list b asg)))
  :induct (len a)
  :enable lookup-equal-list)

(defruled fsa-len-of-flatten
  (implies (id-bitrows-p bitrows)
           (equal (len (fsa-id-flatten bitrows)) (* 8 (len bitrows))))
  :induct (fsa-id-flatten bitrows)
  :enable (fsa-id-flatten id-bitrows-p))

(defruled fsa-symbol-listp-of-flatten
  (implies (id-bitrows-p bitrows)
           (symbol-listp (fsa-id-flatten bitrows)))
  :induct (fsa-id-flatten bitrows)
  :enable (fsa-id-flatten id-bitrows-p))

(defruled fsa-rows-bitsp-from-flat
  (implies (and (id-bitrows-p bitrows)
                (bit-listp (lookup-equal-list (fsa-id-flatten bitrows) asg)))
           (id-rows-bitsp bitrows asg))
  :induct (fsa-id-flatten bitrows)
  :enable (fsa-id-flatten id-bitrows-p id-rows-bitsp fsa-lookup-list-append))

(defruledl fsa-lebits-to-bytes-of-append-8
  (implies (equal (len a) 8)
           (equal (values-lebits-to-bytes (append a b))
                  (cons (lebits=>nat a) (values-lebits-to-bytes b))))
  :expand ((values-lebits-to-bytes (append a b)))
  :prep-books ((include-book "kestrel/lists-light/nthcdr" :dir :system)))

(defruled fsa-flat-lookup-is-decode
  (implies (and (id-bitrows-p bitrows)
                (id-rows-bitsp bitrows asg))
           (equal (values-lebits-to-bytes
                   (lookup-equal-list (fsa-id-flatten bitrows) asg))
                  (id-decode-rows bitrows asg)))
  :induct (fsa-id-flatten bitrows)
  :enable (fsa-id-flatten id-bitrows-p id-rows-bitsp id-decode-rows
           fsa-lookup-list-append fsa-lebits-to-bytes-of-append-8
           len-of-lookup-equal-list lookup-equal-list
           values-lebits-to-bytes))

(defruled fsa-resize-of-append
  (implies (and (bit-listp a) (equal (len a) n))
           (equal (values-bits-resize (append a b) n) a))
  :induct (nth n a)
  :enable (values-bits-resize bit-listp))

(defruled fsa-flat-bits-when-rows-bitsp
  (implies (and (id-bitrows-p bitrows)
                (id-rows-bitsp bitrows asg))
           (bit-listp (lookup-equal-list (fsa-id-flatten bitrows) asg)))
  :induct (fsa-id-flatten bitrows)
  :enable (fsa-id-flatten id-bitrows-p id-rows-bitsp fsa-lookup-list-append
           lookup-equal-list))

(defruled fsa-rows-boundp-bits
  (implies (and (equal (len bitrows) (len witrows))
                (id-rows-boundp bitrows witrows asg))
           (id-bitrows-all-boundp bitrows asg))
  :use id-bitrows-bound-from-rows)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro fsa-idlit-hyps (&rest more)
  `(and (id-bitrows-p bitrows)
        (id-witrows-p witrows)
        (equal (len bitrows) 31)
        (equal (len witrows) 31)
        (symbol-listp excess)
        (< (len excess) (base-prime))
        (symbolp partial) (symbolp uscore) (symbolp islet)
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg partial)
        (r1cs::valuation-bindsp asg uscore)
        (r1cs::valuation-bindsp asg islet)
        (id-rows-boundp bitrows witrows asg)
        (r1cs::valuation-binds-allp asg excess)
        ,@more))

(defruled fsa-idlit-from-bits-le-of-decoded
  (implies (and (id-bitrows-p bitrows)
                (equal (len bitrows) 31)
                (id-rows-bitsp bitrows asg)
                (bit-listp ex)
                (or (endp ex) (values-bits-all-zero-p ex)))
           (equal (identifier-literal-from-bits-le
                   (append (lookup-equal-list (fsa-id-flatten bitrows) asg)
                           ex))
                  (identifier-literal-new
                   (make-identifier-literal
                    :bytes (id-decode-rows bitrows asg)))))
  :do-not-induct t
  :enable (identifier-literal-from-bits-le
           fsa-flat-bits-when-rows-bitsp
           len-of-lookup-equal-list
           fsa-len-of-flatten)
  :use ((:instance fsa-resize-of-append
                   (a (lookup-equal-list (fsa-id-flatten bitrows) asg))
                   (b ex) (n 248))
        fsa-flat-lookup-is-decode)
  :prep-books ((include-book "kestrel/lists-light/nthcdr" :dir :system)))

(defruled fsa-idlit-from-bits-le-gadget-sound
  :short "Over the wires, given @('Boolean::new') on each input bit: the
          result is the identifier literal of the bytes the first 248 bit
          wires form, and @('identifier-literal-from-bits-le') of the input
          bits returns it (so the error case has no satisfying assignment)."
  (implies (fsa-idlit-hyps
            (bit-listp (lookup-equal-list (fsa-id-flatten bitrows) asg))
            (bit-listp (lookup-equal-list excess asg))
            (r1cs::r1cs-constraints-holdp
             (fsa-idlit-from-bits-le-gadget bitrows excess witrows
                                            partial uscore islet p)
             asg p))
           (b* ((lit (make-identifier-literal
                      :bytes (id-decode-rows bitrows asg))))
             (equal (identifier-literal-from-bits-le
                     (lookup-equal-list (append (fsa-id-flatten bitrows) excess)
                                        asg))
                    lit)))
  :do-not-induct t
  :in-theory (e/d (fsa-idlit-from-bits-le-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   fsa-lookup-list-append)
                  (identifier-new-gadget
                   fsa-idlit-validate-gadget
                   idlit-from-bits-le-gadget
                   identifier-literal-from-bits-le))
  :use (fsa-rows-bitsp-from-flat
        fsa-rows-boundp-bits
        id-decode-rows-facts
        id-decode-rows-matchp
        idlit-from-bits-le-gadget-sound-bounded
        fsa-id-new-gadget-as-validate
        (:instance id-bit-checks-complete
                   (bytes (id-decode-rows bitrows asg)))
        (:instance fsa-idlit-from-bits-le-of-decoded
                   (ex (lookup-equal-list excess asg)))
        (:instance identifier-literal-new-sound
                   (x (make-identifier-literal
                       :bytes (id-decode-rows bitrows asg))))))

(defruled fsa-idlit-from-bits-be-gadget-sound
  :short "@('from_bits_be') reverses its input; the wires of the
          reversed list are the same constraint system."
  (implies (fsa-idlit-hyps
            (bit-listp (lookup-equal-list (fsa-id-flatten bitrows) asg))
            (bit-listp (lookup-equal-list excess asg))
            (r1cs::r1cs-constraints-holdp
             (fsa-idlit-from-bits-le-gadget bitrows excess witrows
                                            partial uscore islet p)
             asg p))
           (equal (identifier-literal-from-bits-be
                   (rev (lookup-equal-list
                         (append (fsa-id-flatten bitrows) excess) asg)))
                  (make-identifier-literal
                   :bytes (id-decode-rows bitrows asg))))
  :do-not-induct t
  :in-theory (e/d (identifier-literal-from-bits-be)
                  (identifier-literal-from-bits-le
                   fsa-idlit-from-bits-le-gadget))
  :use fsa-idlit-from-bits-le-gadget-sound)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fsa-validate-ok-when-new-ok
  (implies (and (identifier-literalp lit)
                (not (reserrp (identifier-literal-new lit))))
           (equal (validate-identifier-bytes (identifier-literal->bytes lit))
                  t))
  :enable (identifier-literal-new validate-identifier-bytes)
  :use ((:instance values-unit-resultp-of-validate-trailing-nulls
                   (null-flags (values-validate-bytes-null-flags
                                (identifier-literal->bytes lit) t)))
        (:instance unit-result-cases
                   (r (validate-trailing-nulls
                       (values-validate-bytes-null-flags
                        (identifier-literal->bytes lit) t)))))
  :disable (values-unit-resultp-of-validate-trailing-nulls
            validate-trailing-nulls values-validate-bytes-null-flags)
  :prep-lemmas
  ((defrule unit-result-cases
     (implies (values-unit-resultp r)
              (or (reserrp r) (equal r t)))
     :rule-classes nil
     :enable values-unit-resultp)))

(defruled fsa-from-bits-le-ok-facts
  (implies (and (id-bitrows-p bitrows)
                (equal (len bitrows) 31)
                (id-rows-bitsp bitrows asg)
                (bit-listp ex)
                (not (reserrp (identifier-literal-from-bits-le
                               (append (lookup-equal-list
                                        (fsa-id-flatten bitrows) asg)
                                       ex)))))
           (and (values-bits-all-zero-p ex)
                (equal (validate-identifier-bytes
                        (id-decode-rows bitrows asg))
                       t)))
  :do-not-induct t
  :in-theory (e/d (identifier-literal-from-bits-le
                   fsa-flat-bits-when-rows-bitsp
                   len-of-lookup-equal-list
                   fsa-len-of-flatten
                   values-bits-all-zero-p)
                  (identifier-literal-new validate-identifier-bytes))
  :use ((:instance fsa-resize-of-append
                   (a (lookup-equal-list (fsa-id-flatten bitrows) asg))
                   (b ex) (n 248))
        fsa-flat-lookup-is-decode
        id-decode-rows-facts
        (:instance fsa-validate-ok-when-new-ok
                   (lit (make-identifier-literal
                         :bytes (id-decode-rows bitrows asg)))))
  :prep-books ((include-book "kestrel/lists-light/nthcdr" :dir :system)))

(defruled fsa-idlit-from-bits-le-gadget-complete
  :short "R1CS-COMPLETE, success half: when the funspec returns a literal,
          the input bit wires, the validate_byte wires of each decoded byte,
          and the first-byte wires satisfy the constraints."
  (b* ((bytes (id-decode-rows bitrows asg)))
    (implies (fsa-idlit-hyps
              (bit-listp (lookup-equal-list (fsa-id-flatten bitrows) asg))
              (bit-listp (lookup-equal-list excess asg))
              (not (reserrp (identifier-literal-from-bits-le
                             (lookup-equal-list
                              (append (fsa-id-flatten bitrows) excess) asg))))
              (id-wits-matchp bytes witrows asg)
              (equal (lookup-equal partial asg)
                     (nth 0 (id-first-wits (values-nat-to-lebits 8 (car bytes)))))
              (equal (lookup-equal uscore asg)
                     (nth 1 (id-first-wits (values-nat-to-lebits 8 (car bytes)))))
              (equal (lookup-equal islet asg)
                     (nth 2 (id-first-wits (values-nat-to-lebits 8 (car bytes))))))
             (r1cs::r1cs-constraints-holdp
              (fsa-idlit-from-bits-le-gadget bitrows excess witrows
                                             partial uscore islet p)
              asg p)))
  :do-not-induct t
  :in-theory (e/d (fsa-idlit-from-bits-le-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   fsa-lookup-list-append
                   fsa-flat-bits-when-rows-bitsp
                   len-of-lookup-equal-list
                   fsa-len-of-flatten)
                  (identifier-new-gadget
                   fsa-idlit-validate-gadget
                   idlit-from-bits-le-gadget
                   identifier-literal-new
                   identifier-literal-from-bits-le
                   validate-identifier-bytes
                   id-first-wits))
  :use (fsa-rows-bitsp-from-flat
        id-decode-rows-facts
        id-decode-rows-matchp
        fsa-id-new-gadget-as-validate
        (:instance idlit-from-bits-le-gadget-complete)
        (:instance fsa-from-bits-le-ok-facts
                   (ex (lookup-equal-list excess asg)))
        (:instance identifier-new-gadget-complete
                   (bytes (id-decode-rows bitrows asg)))))

(defruled fsa-idlit-from-bits-be-gadget-complete
  (b* ((bytes (id-decode-rows bitrows asg)))
    (implies (fsa-idlit-hyps
              (bit-listp (lookup-equal-list (fsa-id-flatten bitrows) asg))
              (bit-listp (lookup-equal-list excess asg))
              (not (reserrp (identifier-literal-from-bits-be
                             (rev (lookup-equal-list
                                   (append (fsa-id-flatten bitrows) excess)
                                   asg)))))
              (id-wits-matchp bytes witrows asg)
              (equal (lookup-equal partial asg)
                     (nth 0 (id-first-wits (values-nat-to-lebits 8 (car bytes)))))
              (equal (lookup-equal uscore asg)
                     (nth 1 (id-first-wits (values-nat-to-lebits 8 (car bytes)))))
              (equal (lookup-equal islet asg)
                     (nth 2 (id-first-wits (values-nat-to-lebits 8 (car bytes))))))
             (r1cs::r1cs-constraints-holdp
              (fsa-idlit-from-bits-le-gadget bitrows excess witrows
                                             partial uscore islet p)
              asg p)))
  :do-not-induct t
  :in-theory (e/d (identifier-literal-from-bits-be)
                  (identifier-literal-from-bits-le
                   fsa-idlit-from-bits-le-gadget
                   id-first-wits))
  :use fsa-idlit-from-bits-le-gadget-complete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled fsa-bit-listp-of-append
  (equal (bit-listp (append a b))
         (and (bit-listp (true-list-fix a)) (bit-listp b)))
  :induct (len a)
  :enable bit-listp)

(defruled fsa-parts-bits
  (implies (and (equal (append a b) c)
                (bit-listp c)
                (true-listp a))
           (and (bit-listp a) (bit-listp b)))
  :use fsa-bit-listp-of-append)

(defruled fsa-field-bits-roundtrip
  (implies (and (bit-listp bs)
                (equal (len bs) 253)
                (fieldp (lebits=>nat bs)))
           (equal (values-field-to-bits-le (lebits=>nat bs)) bs))
  :do-not-induct t
  :use ((:instance acl2::nat=>lebits-of-lebits=>nat (digits bs))
        (:instance values-lebits=>nat-upper-bound (bits bs)))
  :enable (values-field-to-bits-le values-nat-to-lebits)
  :disable (acl2::nat=>lebits-of-lebits=>nat values-lebits=>nat-upper-bound)
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)))

(defruled fsa-values-field-to-bits-le-is-field-bits-le
  (implies (fieldp x)
           (equal (values-field-to-bits-le x) (field-bits-le x)))
  :enable (values-field-to-bits-le values-nat-to-lebits field-bits-le
           fieldp pfield::fep base-field-size-in-bits)
  :prep-books ((include-book "kestrel/arithmetic-light/mod" :dir :system)))

(defruled fsa-e-prime-facts
  (and (primep (base-prime)) (oddp (base-prime))
       (equal (integer-length (base-prime)) 253))
  :in-theory '((:e base-prime) (:e primep) (:e oddp)
               (:e integer-length)))

(defmacro fsa-field-hyps ()
  `(and (symbolp x) (symbol-listp rs) (symbolp u)
        (equal (len excess) 5)
        (equal (len rs) (bits-lt-prime-rlen p))
        (r1cs::valuation-bindsp asg x)
        (r1cs::valuation-binds-allp asg rs)
        (r1cs::valuation-bindsp asg u)
        (equal (lookup-equal u asg) 1)))

(defruled fsa-flat-binds
  (implies (and (id-bitrows-p bitrows)
                (equal (len bitrows) (len witrows))
                (id-rows-boundp bitrows witrows asg))
           (r1cs::valuation-binds-allp asg (fsa-id-flatten bitrows)))
  :induct (id-rows-boundp bitrows witrows asg)
  :enable (id-rows-boundp fsa-id-flatten id-bitrows-p
           r1cs::valuation-binds-allp-of-append))

(defruled fsa-idlit-from-field-gadget-sound
  :short "@('IdentifierLiteral::from_field') over the wires, with the public
          unit wire 1: the result is the literal of the bytes the low 248
          bit wires form, and @('identifier-literal-from-field') of the input
          returns it."
  (implies (fsa-idlit-hyps
            (fsa-field-hyps)
            (r1cs::r1cs-constraints-holdp
             (fsa-idlit-from-field-gadget x rs u bitrows excess witrows
                                          partial uscore islet p)
             asg p))
           (equal (identifier-literal-from-field (lookup-equal x asg))
                  (make-identifier-literal
                   :bytes (id-decode-rows bitrows asg))))
  :do-not-induct t
  :in-theory (e/d (fsa-idlit-from-field-gadget
                   identifier-literal-from-field
                   r1cs::r1cs-constraints-holdp-of-append
                   fsa-lookup-list-append
                   fsa-bit-listp-of-append
                   fsa-len-of-flatten
                   fsa-symbol-listp-of-flatten
                   r1cs::valuation-binds-allp-of-append
                   len-of-lookup-equal-list
                   r1cs::fep-of-lookup-equal
                   fieldp)
                  (identifier-literal-from-bits-le
                   fsa-idlit-from-bits-le-gadget
                   field-to-bits-gadget
                   values-field-to-bits-le))
  :use (fsa-flat-binds
        fsa-e-prime-facts
        (:instance field-to-bits-soundness
                   (xs (append (fsa-id-flatten bitrows) excess)))
        (:instance fsa-field-bits-roundtrip
                   (bs (lookup-equal-list
                        (append (fsa-id-flatten bitrows) excess) asg)))
        fsa-idlit-from-bits-le-gadget-sound))

(defruled fsa-idlit-from-field-gadget-complete
  :short "R1CS-COMPLETE, success half, of @('IdentifierLiteral::from_field'):
          the canonical field bits, the bits-lte-const fold witness, the
          public unit 1, and the byte-validation witnesses."
  (b* ((bytes (id-decode-rows bitrows asg))
       (xs (append (fsa-id-flatten bitrows) excess)))
    (implies (fsa-idlit-hyps
              (fsa-field-hyps)
              (fieldp (lookup-equal x asg))
              (equal (lookup-equal-list xs asg)
                     (field-bits-le (lookup-equal x asg)))
              (equal (lookup-equal-list rs asg)
                     (fb-bits-lte-const-witness
                      (lookup-equal-list xs asg)
                      (nat=>lebits* (1- p))))
              (not (reserrp (identifier-literal-from-field
                             (lookup-equal x asg))))
              (id-wits-matchp bytes witrows asg)
              (equal (lookup-equal partial asg)
                     (nth 0 (id-first-wits (values-nat-to-lebits 8 (car bytes)))))
              (equal (lookup-equal uscore asg)
                     (nth 1 (id-first-wits (values-nat-to-lebits 8 (car bytes)))))
              (equal (lookup-equal islet asg)
                     (nth 2 (id-first-wits (values-nat-to-lebits 8 (car bytes))))))
             (r1cs::r1cs-constraints-holdp
              (fsa-idlit-from-field-gadget x rs u bitrows excess witrows
                                           partial uscore islet p)
              asg p)))
  :do-not-induct t
  :in-theory (e/d (fsa-idlit-from-field-gadget
                   identifier-literal-from-field
                   fb-field-write-bits-le-gadget
                   r1cs::r1cs-constraints-holdp-of-append
                   fsa-lookup-list-append
                   fsa-len-of-flatten
                   fsa-symbol-listp-of-flatten
                   r1cs::valuation-binds-allp-of-append)
                  (identifier-literal-from-bits-le
                   fsa-idlit-from-bits-le-gadget
                   field-to-bits-gadget
                   values-field-to-bits-le
                   field-bits-le
                   id-first-wits))
  :use (fsa-flat-binds
        fsa-e-prime-facts
        (:instance fsa-parts-bits
                   (a (lookup-equal-list (fsa-id-flatten bitrows) asg))
                   (b (lookup-equal-list excess asg))
                   (c (field-bits-le (lookup-equal x asg))))
        (:instance bit-listp-of-field-bits-le (x (lookup-equal x asg)))
        (:instance fsa-values-field-to-bits-le-is-field-bits-le
                   (x (lookup-equal x asg)))
        (:instance fb2-field-write-bits-le-gadget-complete
                   (bits (append (fsa-id-flatten bitrows) excess)))
        fsa-idlit-from-bits-le-gadget-complete))
