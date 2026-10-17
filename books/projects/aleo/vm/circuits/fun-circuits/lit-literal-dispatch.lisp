;AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Literal::is_equal, Literal::is_not_equal, Literal::write_bits_le and
; Literal::write_bits_be: the full dispatch.
;
; Each of these is a host match on the variants
; (circuit/program/src/data/literal/{equal,to_bits}.rs).  For is_equal and
; is_not_equal, equal variants call the per-type circuit and mismatched
; variants return a constant (lit-literal-equal.lisp).  For write_bits, each
; variant calls the per-type circuit.  So the R1CS of a Literal operation is
; the R1CS of the selected per-type circuit, and each theorem below restates
; the per-type wire-soundness theorem with the Literal funspec applied to the
; literal the wires denote.  The hypotheses are those of the per-type
; theorem (copied from the world by lit-compose) plus the type facts that
; Literal::new establishes for the variant.  Completeness of each arm is the
; per-type completeness theorem (the gadget is the same); the bridges below
; identify its output with the Literal funspec.  The Signature arm is in
; lit-literal-signature.lisp.

(in-package "ALEOVM")

(include-book "lit-literal-signature")
(include-book "lit-literal-equal")
(include-book "lit-identifier-bits")
(include-book "group-wire-sound")
(include-book "fb-field-eq")
(include-book "crv-field")
(include-book "int-equal")
(include-book "val-string-ops")
(include-book "fsa-identifier-literal-bits")
(include-book "fb-field-bits")
(include-book "../r1cs/boolean-xor")

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/lists/rev" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (lit-compose name base :subst s :hyps h :concl c :enable e) proves
; (implies (and H h) c), where H is the hypothesis of the theorem base after
; substituting s, using base and the rules e.

(defun lit-compose-fn (name base subst hyps concl enable wrld)
  (declare (xargs :mode :program))
  (b* ((f (acl2::formula base nil wrld))
       (f (acl2::sublis-var subst f))
       (h (if (eq (car f) 'implies) (acl2::untranslate (cadr f) t wrld) t)))
    `(defruled ,name
       (implies (and ,h ,@hyps) ,concl)
       :hints (("Goal"
                :do-not-induct t
                :use ((:instance ,base
                                 ,@(pairlis$ (strip-cars subst)
                                             (pairlis$ (strip-cdrs subst) nil))))
                :in-theory '(,@enable))))))

(defmacro lit-compose (name base &key subst hyps concl enable)
  `(make-event (lit-compose-fn ',name ',base ',subst ',hyps ',concl ',enable
                               (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Value-level dispatch: on equal variants the Literal funspecs are the
; per-type funspecs.

(defmacro lit-eq-bridges (kind pred fn-eq fn-neq &key enable)
  (b* ((lit (intern-in-package-of-symbol
             (concatenate 'string "LITERAL-" (symbol-name kind)) 'lit-compose))
       (n-eq (intern-in-package-of-symbol
              (concatenate 'string "LIT-LITERAL-IS-EQUAL-" (symbol-name kind) "-BRIDGE")
              'lit-compose))
       (n-neq (intern-in-package-of-symbol
               (concatenate 'string "LIT-LITERAL-IS-NOT-EQUAL-" (symbol-name kind) "-BRIDGE")
               'lit-compose)))
    `(progn
       (defruled ,n-eq
         (implies (and (,pred a) (,pred b))
                  (equal (literal-is-equal (,lit a) (,lit b)) ,fn-eq))
         :enable (literal-is-equal values-literal-equalp values-bool-to-bit
                  ,@enable))
       (defruled ,n-neq
         (implies (and (,pred a) (,pred b))
                  (equal (literal-is-not-equal (,lit a) (,lit b)) ,fn-neq))
         :enable (literal-is-not-equal values-literal-equalp values-bool-to-bit
                  ,@enable)))))

(lit-eq-bridges address groupp
                (address-is-equal-funspec a b) (address-is-not-equal-funspec a b)
                :enable (address-is-equal-funspec address-is-not-equal-funspec
                         group-is-equal-funspec group-is-not-equal-funspec))

(lit-eq-bridges group groupp
                (group-is-equal-funspec a b) (group-is-not-equal-funspec a b)
                :enable (group-is-equal-funspec group-is-not-equal-funspec))

(lit-eq-bridges field fieldp
                (field-is-equal-funspec a b) (field-is-not-equal-funspec a b)
                :enable (field-is-equal-funspec field-is-not-equal-funspec
                         boolean-not-funspec))

(lit-eq-bridges scalar scalarp
                (scalar-is-equal-funspec a b) (scalar-is-not-equal-funspec a b)
                :enable (scalar-is-equal-funspec scalar-is-not-equal-funspec
                         boolean-not-funspec))

(lit-eq-bridges boolean bitp
                (if (equal a b) 1 0) (bitxor a b)
                :enable (bitxor bitp))

(lit-eq-bridges string string-typep
                (string-type-is-equal a b)
                (string-type-is-not-equal a b)
                :enable (string-type-is-not-equal values-b-not))

(lit-eq-bridges identifier identifier-literalp
                (identifier-literal-is-equal a b)
                (identifier-literal-is-not-equal a b)
                :enable (identifier-literal-is-equal identifier-literal-is-not-equal))

(defmacro lit-int-bridges (lit bytep signedp n n-typ n-eq n-neq)
  `(progn
       (defruled ,n-typ
         (implies (int-valuep x ,signedp ,n) (,bytep x))
         :enable (int-valuep int-min int-max ,bytep
                  signed-byte-p unsigned-byte-p integer-range-p))
       (defruled ,n-eq
         (implies (and (int-valuep a ,signedp ,n) (int-valuep b ,signedp ,n))
                  (equal (literal-is-equal (,lit a) (,lit b))
                         (int-is-equal-spec a b ,signedp ,n)))
         :enable (literal-is-equal values-literal-equalp values-bool-to-bit
                  int-is-equal-spec int-spec-bool)
         :use ((:instance ,n-typ (x a)) (:instance ,n-typ (x b))))
       (defruled ,n-neq
         (implies (and (int-valuep a ,signedp ,n) (int-valuep b ,signedp ,n))
                  (equal (literal-is-not-equal (,lit a) (,lit b))
                         (int-is-not-equal-spec a b ,signedp ,n)))
         :enable (literal-is-not-equal values-literal-equalp values-bool-to-bit
                  int-is-not-equal-spec int-spec-bool)
         :use ((:instance ,n-typ (x a)) (:instance ,n-typ (x b))))))

(lit-int-bridges literal-i8 acl2::sbyte8p t 8
                 lit-i8-bytep-when-int-valuep
                 lit-literal-is-equal-i8-bridge lit-literal-is-not-equal-i8-bridge)
(lit-int-bridges literal-i16 acl2::sbyte16p t 16
                 lit-i16-bytep-when-int-valuep
                 lit-literal-is-equal-i16-bridge lit-literal-is-not-equal-i16-bridge)
(lit-int-bridges literal-i32 acl2::sbyte32p t 32
                 lit-i32-bytep-when-int-valuep
                 lit-literal-is-equal-i32-bridge lit-literal-is-not-equal-i32-bridge)
(lit-int-bridges literal-i64 acl2::sbyte64p t 64
                 lit-i64-bytep-when-int-valuep
                 lit-literal-is-equal-i64-bridge lit-literal-is-not-equal-i64-bridge)
(lit-int-bridges literal-i128 acl2::sbyte128p t 128
                 lit-i128-bytep-when-int-valuep
                 lit-literal-is-equal-i128-bridge lit-literal-is-not-equal-i128-bridge)
(lit-int-bridges literal-u8 acl2::ubyte8p nil 8
                 lit-u8-bytep-when-int-valuep
                 lit-literal-is-equal-u8-bridge lit-literal-is-not-equal-u8-bridge)
(lit-int-bridges literal-u16 acl2::ubyte16p nil 16
                 lit-u16-bytep-when-int-valuep
                 lit-literal-is-equal-u16-bridge lit-literal-is-not-equal-u16-bridge)
(lit-int-bridges literal-u32 acl2::ubyte32p nil 32
                 lit-u32-bytep-when-int-valuep
                 lit-literal-is-equal-u32-bridge lit-literal-is-not-equal-u32-bridge)
(lit-int-bridges literal-u64 acl2::ubyte64p nil 64
                 lit-u64-bytep-when-int-valuep
                 lit-literal-is-equal-u64-bridge lit-literal-is-not-equal-u64-bridge)
(lit-int-bridges literal-u128 acl2::ubyte128p nil 128
                 lit-u128-bytep-when-int-valuep
                 lit-literal-is-equal-u128-bridge lit-literal-is-not-equal-u128-bridge)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; is_equal / is_not_equal per arm over the wires.

(lit-compose lit-literal-is-equal-address-sound crv-address-is-equal-wire-sound
             :hyps ((groupp p1) (groupp p2))
             :concl (equal (lookup-equal out asg)
                           (literal-is-equal (literal-address p1) (literal-address p2)))
             :enable (lit-literal-is-equal-address-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-address-sound crv-address-is-not-equal-wire-sound
             :hyps ((groupp p1) (groupp p2))
             :concl (equal (pfield::sub 1 (lookup-equal out asg) p)
                           (literal-is-not-equal (literal-address p1) (literal-address p2)))
             :enable (lit-literal-is-not-equal-address-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-group-sound crv-group-is-equal-wire-sound
             :hyps ((groupp p1) (groupp p2))
             :concl (equal (lookup-equal out asg)
                           (literal-is-equal (literal-group p1) (literal-group p2)))
             :enable (lit-literal-is-equal-group-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-group-sound crv-group-is-not-equal-wire-sound
             :hyps ((groupp p1) (groupp p2))
             :concl (equal (pfield::sub 1 (lookup-equal out asg) p)
                           (literal-is-not-equal (literal-group p1) (literal-group p2)))
             :enable (lit-literal-is-not-equal-group-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-field-sound field-is-equal-gadget-sound
             :concl (equal (pfield::sub 1 (lookup-equal r asg) p)
                           (literal-is-equal (literal-field (lookup-equal x asg)) (literal-field (lookup-equal y asg))))
             :enable (lit-literal-is-equal-field-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-field-sound crv-field-is-not-equal-gadget-sound
             :concl (equal (lookup-equal r asg)
                           (literal-is-not-equal (literal-field (lookup-equal x asg)) (literal-field (lookup-equal y asg))))
             :enable (lit-literal-is-not-equal-field-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-scalar-sound crv-scalar-is-equal-gadget-sound
             :concl (equal (pfield::sub 1 (lookup-equal r asg) p)
                           (literal-is-equal (literal-scalar (lookup-equal a asg)) (literal-scalar (lookup-equal b asg))))
             :enable (lit-literal-is-equal-scalar-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-scalar-sound crv-scalar-is-not-equal-gadget-sound
             :concl (equal (lookup-equal r asg)
                           (literal-is-not-equal (literal-scalar (lookup-equal a asg)) (literal-scalar (lookup-equal b asg))))
             :enable (lit-literal-is-not-equal-scalar-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-i8-sound int-is-equal-gadget-sound
             :subst ((signedp . 't) (n . '8))
             :concl (equal (pfield::sub 1 (lookup-equal z asg) p)
                           (literal-is-equal (literal-i8 x) (literal-i8 y)))
             :enable (lit-literal-is-equal-i8-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-i8-sound int-is-not-equal-gadget-sound
             :subst ((signedp . 't) (n . '8))
             :concl (equal (lookup-equal z asg)
                           (literal-is-not-equal (literal-i8 x) (literal-i8 y)))
             :enable (lit-literal-is-not-equal-i8-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-i16-sound int-is-equal-gadget-sound
             :subst ((signedp . 't) (n . '16))
             :concl (equal (pfield::sub 1 (lookup-equal z asg) p)
                           (literal-is-equal (literal-i16 x) (literal-i16 y)))
             :enable (lit-literal-is-equal-i16-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-i16-sound int-is-not-equal-gadget-sound
             :subst ((signedp . 't) (n . '16))
             :concl (equal (lookup-equal z asg)
                           (literal-is-not-equal (literal-i16 x) (literal-i16 y)))
             :enable (lit-literal-is-not-equal-i16-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-i32-sound int-is-equal-gadget-sound
             :subst ((signedp . 't) (n . '32))
             :concl (equal (pfield::sub 1 (lookup-equal z asg) p)
                           (literal-is-equal (literal-i32 x) (literal-i32 y)))
             :enable (lit-literal-is-equal-i32-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-i32-sound int-is-not-equal-gadget-sound
             :subst ((signedp . 't) (n . '32))
             :concl (equal (lookup-equal z asg)
                           (literal-is-not-equal (literal-i32 x) (literal-i32 y)))
             :enable (lit-literal-is-not-equal-i32-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-i64-sound int-is-equal-gadget-sound
             :subst ((signedp . 't) (n . '64))
             :concl (equal (pfield::sub 1 (lookup-equal z asg) p)
                           (literal-is-equal (literal-i64 x) (literal-i64 y)))
             :enable (lit-literal-is-equal-i64-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-i64-sound int-is-not-equal-gadget-sound
             :subst ((signedp . 't) (n . '64))
             :concl (equal (lookup-equal z asg)
                           (literal-is-not-equal (literal-i64 x) (literal-i64 y)))
             :enable (lit-literal-is-not-equal-i64-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-i128-sound int-is-equal-gadget-sound
             :subst ((signedp . 't) (n . '128))
             :concl (equal (pfield::sub 1 (lookup-equal z asg) p)
                           (literal-is-equal (literal-i128 x) (literal-i128 y)))
             :enable (lit-literal-is-equal-i128-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-i128-sound int-is-not-equal-gadget-sound
             :subst ((signedp . 't) (n . '128))
             :concl (equal (lookup-equal z asg)
                           (literal-is-not-equal (literal-i128 x) (literal-i128 y)))
             :enable (lit-literal-is-not-equal-i128-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-u8-sound int-is-equal-gadget-sound
             :subst ((signedp . 'nil) (n . '8))
             :concl (equal (pfield::sub 1 (lookup-equal z asg) p)
                           (literal-is-equal (literal-u8 x) (literal-u8 y)))
             :enable (lit-literal-is-equal-u8-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-u8-sound int-is-not-equal-gadget-sound
             :subst ((signedp . 'nil) (n . '8))
             :concl (equal (lookup-equal z asg)
                           (literal-is-not-equal (literal-u8 x) (literal-u8 y)))
             :enable (lit-literal-is-not-equal-u8-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-u16-sound int-is-equal-gadget-sound
             :subst ((signedp . 'nil) (n . '16))
             :concl (equal (pfield::sub 1 (lookup-equal z asg) p)
                           (literal-is-equal (literal-u16 x) (literal-u16 y)))
             :enable (lit-literal-is-equal-u16-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-u16-sound int-is-not-equal-gadget-sound
             :subst ((signedp . 'nil) (n . '16))
             :concl (equal (lookup-equal z asg)
                           (literal-is-not-equal (literal-u16 x) (literal-u16 y)))
             :enable (lit-literal-is-not-equal-u16-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-u32-sound int-is-equal-gadget-sound
             :subst ((signedp . 'nil) (n . '32))
             :concl (equal (pfield::sub 1 (lookup-equal z asg) p)
                           (literal-is-equal (literal-u32 x) (literal-u32 y)))
             :enable (lit-literal-is-equal-u32-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-u32-sound int-is-not-equal-gadget-sound
             :subst ((signedp . 'nil) (n . '32))
             :concl (equal (lookup-equal z asg)
                           (literal-is-not-equal (literal-u32 x) (literal-u32 y)))
             :enable (lit-literal-is-not-equal-u32-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-u64-sound int-is-equal-gadget-sound
             :subst ((signedp . 'nil) (n . '64))
             :concl (equal (pfield::sub 1 (lookup-equal z asg) p)
                           (literal-is-equal (literal-u64 x) (literal-u64 y)))
             :enable (lit-literal-is-equal-u64-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-u64-sound int-is-not-equal-gadget-sound
             :subst ((signedp . 'nil) (n . '64))
             :concl (equal (lookup-equal z asg)
                           (literal-is-not-equal (literal-u64 x) (literal-u64 y)))
             :enable (lit-literal-is-not-equal-u64-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-u128-sound int-is-equal-gadget-sound
             :subst ((signedp . 'nil) (n . '128))
             :concl (equal (pfield::sub 1 (lookup-equal z asg) p)
                           (literal-is-equal (literal-u128 x) (literal-u128 y)))
             :enable (lit-literal-is-equal-u128-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-u128-sound int-is-not-equal-gadget-sound
             :subst ((signedp . 'nil) (n . '128))
             :concl (equal (lookup-equal z asg)
                           (literal-is-not-equal (literal-u128 x) (literal-u128 y)))
             :enable (lit-literal-is-not-equal-u128-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-string-sound string-is-equal-gadget-sound
             :concl (equal (lookup-equal out asg)
                           (literal-is-equal (literal-string s) (literal-string u)))
             :enable (lit-literal-is-equal-string-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-string-sound string-is-not-equal-gadget-sound
             :concl (equal (pfield::sub 1 (lookup-equal out asg) p)
                           (literal-is-not-equal (literal-string s) (literal-string u)))
             :enable (lit-literal-is-not-equal-string-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-equal-identifier-sound idlit-is-equal-gadget-sound
             :concl (equal (pfield::sub 1 (lookup-equal r asg) p)
                           (literal-is-equal (literal-identifier a) (literal-identifier b)))
             :enable (lit-literal-is-equal-identifier-bridge lit-fieldp-of-lookup-wire))
(lit-compose lit-literal-is-not-equal-identifier-sound idlit-is-not-equal-gadget-sound
             :concl (equal (lookup-equal r asg)
                           (literal-is-not-equal (literal-identifier a) (literal-identifier b)))
             :enable (lit-literal-is-not-equal-identifier-bridge lit-fieldp-of-lookup-wire))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Boolean arm.  Boolean::is_not_equal is a ^ b, the single constraint
; (a + a) * b = a + b - out (boolean-xor-gadget); Boolean::is_equal is
; !(a ^ b), the linear combination 1 - out.  The input wires are bits by
; Boolean::new.

(define lit-boolean-is-not-equal-gadget ((a symbolp) (b symbolp) (out symbolp)
                                         (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  :short "Constraints of @('Boolean::is_not_equal') and
          @('Boolean::is_equal') (the same constraint)."
  (boolean-xor-gadget a b out p))

(defmacro lit-boolean-hyps (&rest more)
  `(and (symbolp a) (symbolp b) (symbolp out)
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-bindsp asg a)
        (r1cs::valuation-bindsp asg b)
        (r1cs::valuation-bindsp asg out)
        (bitp (lookup-equal a asg))
        (bitp (lookup-equal b asg))
        ,@more))

(defruled lit-boolean-xor-arith
  (implies (and (bitp a) (bitp b))
           (and (bitp (bitxor a b))
                (equal (pfield::sub 1 (bitxor a b) (base-prime))
                       (if (equal a b) 1 0))))
  :enable (bitxor bitp))

(defruled lit-literal-is-not-equal-boolean-sound
  (implies (lit-boolean-hyps
            (r1cs::r1cs-constraints-holdp
             (lit-boolean-is-not-equal-gadget a b out p) asg p))
           (equal (lookup-equal out asg)
                  (literal-is-not-equal (literal-boolean (lookup-equal a asg))
                                        (literal-boolean (lookup-equal b asg)))))
  :enable (lit-boolean-is-not-equal-gadget
           lit-literal-is-not-equal-boolean-bridge)
  :use (:instance boolean-xor-gadget-to-bitxor (x a) (y b) (z out)))

(defruled lit-literal-is-equal-boolean-sound
  (implies (lit-boolean-hyps
            (r1cs::r1cs-constraints-holdp
             (lit-boolean-is-not-equal-gadget a b out p) asg p))
           (equal (pfield::sub 1 (lookup-equal out asg) p)
                  (literal-is-equal (literal-boolean (lookup-equal a asg))
                                    (literal-boolean (lookup-equal b asg)))))
  :enable (lit-boolean-is-not-equal-gadget
           lit-literal-is-equal-boolean-bridge)
  :disable ((:definition pfield::sub))
  :use ((:instance boolean-xor-gadget-to-bitxor (x a) (y b) (z out))
        (:instance lit-boolean-xor-arith
                   (a (lookup-equal a asg)) (b (lookup-equal b asg)))))

(defruled lit-literal-boolean-equal-complete
  (implies (lit-boolean-hyps
            (equal (lookup-equal out asg)
                   (bitxor (lookup-equal a asg) (lookup-equal b asg))))
           (r1cs::r1cs-constraints-holdp
            (lit-boolean-is-not-equal-gadget a b out p) asg p))
  :enable lit-boolean-is-not-equal-gadget
  :use (:instance boolean-xor-gadget-to-bitxor (x a) (y b) (z out)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; write_bits_le / write_bits_be: value-level dispatch.

(defruled lit-literal-to-bits-address-bridge
  (implies (groupp g)
           (and (equal (literal-to-bits-le (literal-address g))
                       (address-write-bits-le-funspec g))
                (equal (literal-to-bits-be (literal-address g))
                       (address-write-bits-be-funspec g))))
  :enable (literal-to-bits-le literal-to-bits-be
           address-write-bits-le-funspec address-write-bits-be-funspec
           lit-values-group-bits-le-is-curve lit-values-group-bits-be-is-rev
           crv-group-write-bits-be-is-rev-le))

(defruled lit-literal-to-bits-group-bridge
  (implies (groupp g)
           (and (equal (literal-to-bits-le (literal-group g))
                       (group-write-bits-le-funspec g))
                (equal (literal-to-bits-be (literal-group g))
                       (group-write-bits-be-funspec g))))
  :enable (literal-to-bits-le literal-to-bits-be
           lit-values-group-bits-le-is-curve lit-values-group-bits-be-is-rev
           crv-group-write-bits-be-is-rev-le))

(defruled lit-literal-to-bits-field-bridge
  (implies (fieldp x)
           (and (equal (literal-to-bits-le (literal-field x))
                       (field-write-bits-le-funspec nil x))
                (equal (literal-to-bits-be (literal-field x))
                       (field-write-bits-be-funspec nil x))))
  :enable (literal-to-bits-le literal-to-bits-be
           field-write-bits-le-funspec field-write-bits-be-funspec
           values-field-to-bits-be
           lit-field-bits-le-is-values-field-to-bits-le))

(defruled lit-literal-to-bits-scalar-bridge
  (implies (scalarp s)
           (and (equal (literal-to-bits-le (literal-scalar s))
                       (scalar-write-bits-le-funspec nil s))
                (equal (literal-to-bits-be (literal-scalar s))
                       (scalar-write-bits-be-funspec nil s))))
  :enable (literal-to-bits-le literal-to-bits-be
           scalar-write-bits-le-funspec scalar-write-bits-be-funspec
           values-scalar-to-bits-be
           lit-values-scalar-bits-le-is-curve lit-scalar-bits-le-is-curve))

(defruled lit-literal-to-bits-boolean-bridge
  (implies (bitp b)
           (and (equal (literal-to-bits-le (literal-boolean b)) (list b))
                (equal (literal-to-bits-be (literal-boolean b)) (list b))))
  :enable (literal-to-bits-le literal-to-bits-be))

(defruled lit-literal-to-bits-string-bridge
  (implies (string-typep s)
           (and (equal (literal-to-bits-le (literal-string s))
                       (string-type-to-bits-le s))
                (equal (literal-to-bits-be (literal-string s))
                       (string-type-to-bits-be s))))
  :enable (literal-to-bits-le literal-to-bits-be))

(defruled lit-literal-to-bits-identifier-bridge
  (implies (identifier-literalp x)
           (and (equal (literal-to-bits-le (literal-identifier x))
                       (identifier-literal-to-bits-le x))
                (equal (literal-to-bits-be (literal-identifier x))
                       (identifier-literal-to-bits-be x))))
  :enable (literal-to-bits-le literal-to-bits-be))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; write_bits_le / write_bits_be per arm over the wires.

(lit-compose lit-literal-write-bits-le-address-sound
             crv-address-write-bits-le-gadget-sound
             :hyps ((groupp p0))
             :concl (equal (lookup-equal-list xs asg)
                           (literal-to-bits-le (literal-address p0)))
             :enable (lit-literal-to-bits-address-bridge))

(lit-compose lit-literal-write-bits-be-address-sound
             crv-address-write-bits-be-gadget-sound
             :hyps ((groupp p0))
             :concl (equal (rev (lookup-equal-list xs asg))
                           (literal-to-bits-be (literal-address p0)))
             :enable (lit-literal-to-bits-address-bridge))

(lit-compose lit-literal-write-bits-le-group-sound
             crv-group-write-bits-le-gadget-sound
             :hyps ((groupp p0))
             :concl (equal (lookup-equal-list xs asg)
                           (literal-to-bits-le (literal-group p0)))
             :enable (lit-literal-to-bits-group-bridge))

(lit-compose lit-literal-write-bits-be-group-sound
             crv-group-write-bits-be-gadget-sound
             :hyps ((groupp p0))
             :concl (equal (rev (lookup-equal-list xs asg))
                           (literal-to-bits-be (literal-group p0)))
             :enable (lit-literal-to-bits-group-bridge))

(lit-compose lit-literal-write-bits-le-field-sound
             fb-field-write-bits-le-gadget-sound
             :subst ((acc . 'nil))
             :concl (equal (lookup-equal-list bits asg)
                           (literal-to-bits-le
                            (literal-field (lookup-equal x asg))))
             :enable (lit-literal-to-bits-field-bridge lit-append-of-nil
                      lit-fieldp-of-lookup-wire))

(lit-compose lit-literal-write-bits-be-field-sound
             fb-field-write-bits-be-gadget-sound
             :subst ((acc . 'nil))
             :concl (equal (rev (lookup-equal-list bits asg))
                           (literal-to-bits-be
                            (literal-field (lookup-equal x asg))))
             :enable (lit-literal-to-bits-field-bridge lit-append-of-nil
                      lit-fieldp-of-lookup-wire))

(lit-compose lit-literal-write-bits-le-scalar-sound
             scalar-write-bits-le-gadget-sound
             :subst ((acc . 'nil))
             :concl (equal (lookup-equal-list xs asg)
                           (literal-to-bits-le
                            (literal-scalar (lookup-equal s asg))))
             :enable (lit-literal-to-bits-scalar-bridge lit-append-of-nil))

(lit-compose lit-literal-write-bits-be-scalar-sound
             scalar-write-bits-be-gadget-sound
             :subst ((acc . 'nil))
             :concl (equal (rev (lookup-equal-list xs asg))
                           (literal-to-bits-be
                            (literal-scalar (lookup-equal s asg))))
             :enable (lit-literal-to-bits-scalar-bridge lit-append-of-nil))

(lit-compose lit-literal-write-bits-le-string-sound
             string-write-bits-le-gadget-sound
             :concl (equal (literal-to-bits-le (literal-string s))
                           (values-bytes-to-lebits (string-type->bytes s)))
             :enable (lit-literal-to-bits-string-bridge))

(lit-compose lit-literal-write-bits-be-string-sound
             string-write-bits-be-gadget-sound
             :concl (equal (literal-to-bits-be (literal-string s))
                           (values-bytes-to-bebits (string-type->bytes s)))
             :enable (lit-literal-to-bits-string-bridge))

(lit-compose lit-literal-write-bits-le-identifier-sound
             fsa-identifier-write-bits-le-wire-sound
             :concl (equal (lookup-equal-list (fsa-id-flatten bitrows) asg)
                           (literal-to-bits-le (literal-identifier x)))
             :enable (lit-literal-to-bits-identifier-bridge))

(lit-compose lit-literal-write-bits-be-identifier-sound
             fsa-identifier-write-bits-be-wire-sound
             :concl (equal (rev (lookup-equal-list (fsa-id-flatten bitrows) asg))
                           (literal-to-bits-be (literal-identifier x)))
             :enable (lit-literal-to-bits-identifier-bridge))

(define lit-literal-write-bits-empty-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of the Boolean and Integer arms of
          @('Literal::write_bits_le') and @('Literal::write_bits_be'): none.
          The bits are the wires of the Boolean or of the Integer."
  nil)

(defruled lit-literal-write-bits-empty-gadget-complete
  (r1cs::r1cs-constraints-holdp (lit-literal-write-bits-empty-gadget) asg p)
  :enable lit-literal-write-bits-empty-gadget)

(defruled lit-literal-write-bits-boolean-sound
  (implies (and (bitp (lookup-equal b asg))
                (r1cs::r1cs-constraints-holdp
                 (lit-literal-write-bits-empty-gadget) asg p))
           (and (equal (list (lookup-equal b asg))
                       (literal-to-bits-le (literal-boolean (lookup-equal b asg))))
                (equal (list (lookup-equal b asg))
                       (literal-to-bits-be (literal-boolean (lookup-equal b asg))))))
  :enable lit-literal-to-bits-boolean-bridge)

(defmacro lit-int-bits-arm (lit signedp n n-typ name)
  `(defruled ,name
     (implies (and (int-valuep x ,signedp ,n)
                   (equal (lookup-equal-list xs asg) (int->lebits x ,n))
                   (r1cs::r1cs-constraints-holdp
                    (lit-literal-write-bits-empty-gadget) asg p))
              (and (equal (lookup-equal-list xs asg)
                          (literal-to-bits-le (,lit x)))
                   (equal (rev (lookup-equal-list xs asg))
                          (literal-to-bits-be (,lit x)))))
     :enable (literal-to-bits-le literal-to-bits-be
              values-int-to-bits-le values-int-to-bits-be
              values-nat-to-bebits values-nat-to-lebits int->lebits)
     :use (:instance ,n-typ)))

(lit-int-bits-arm literal-i8 t 8 lit-i8-bytep-when-int-valuep
                  lit-literal-write-bits-i8-sound)
(lit-int-bits-arm literal-i16 t 16 lit-i16-bytep-when-int-valuep
                  lit-literal-write-bits-i16-sound)
(lit-int-bits-arm literal-i32 t 32 lit-i32-bytep-when-int-valuep
                  lit-literal-write-bits-i32-sound)
(lit-int-bits-arm literal-i64 t 64 lit-i64-bytep-when-int-valuep
                  lit-literal-write-bits-i64-sound)
(lit-int-bits-arm literal-i128 t 128 lit-i128-bytep-when-int-valuep
                  lit-literal-write-bits-i128-sound)
(lit-int-bits-arm literal-u8 nil 8 lit-u8-bytep-when-int-valuep
                  lit-literal-write-bits-u8-sound)
(lit-int-bits-arm literal-u16 nil 16 lit-u16-bytep-when-int-valuep
                  lit-literal-write-bits-u16-sound)
(lit-int-bits-arm literal-u32 nil 32 lit-u32-bytep-when-int-valuep
                  lit-literal-write-bits-u32-sound)
(lit-int-bits-arm literal-u64 nil 64 lit-u64-bytep-when-int-valuep
                  lit-literal-write-bits-u64-sound)
(lit-int-bits-arm literal-u128 nil 128 lit-u128-bytep-when-int-valuep
                  lit-literal-write-bits-u128-sound)
