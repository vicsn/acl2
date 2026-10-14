; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specifications of snarkVM's circuit OutputID and Response
; (circuit/program/src/response).

(in-package "ALEOVM")

(include-book "crypto-request")

(local (include-book "arithmetic-5/top" :dir :system))

(local (in-theory (disable bitp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types.

; snarkVM circuit/program/src/response/mod.rs: enum OutputID.
(fty::deftagsum crypto-output-id
  (:constant ((hash values-field)))
  (:public ((hash values-field)))
  (:private ((hash values-field)))
  (:record ((commitment values-field)
            (checksum values-field)
            (sender-ciphertext values-field)))
  (:external-record ((hash values-field)))
  (:future ((hash values-field)))
  (:dynamic-record ((hash values-field)))
  (:dynamic-future ((hash values-field)))
  :pred crypto-output-idp)

(fty::deflist crypto-output-id-list
  :elt-type crypto-output-id
  :true-listp t
  :elementp-of-nil nil
  :pred crypto-output-id-listp)

(fty::defresult crypto-output-id-result
  :ok crypto-output-id
  :pred crypto-output-id-resultp
  :prepwork ((local (in-theory (enable crypto-output-id-kind)))))

; snarkVM circuit/program/src/response/mod.rs: struct Response.
(fty::defprod crypto-response
  ((output-ids crypto-output-id-list)
   (outputs crypto-value-list))
  :tag :crypto-response
  :pred crypto-responsep)

(fty::defresult crypto-response-result
  :ok crypto-response
  :pred crypto-response-resultp)

(fty::defresult crypto-value-list-result
  :ok crypto-value-list
  :pred crypto-value-list-resultp)

; Output registers (Option<Register>): nil for None, or the register locator.
(define crypto-output-register-listp (x)
  :returns (yes/no booleanp)
  (or (null x)
      (and (consp x)
           (or (null (car x)) (unsigned-byte-p 64 (car x)))
           (crypto-output-register-listp (cdr x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; OutputID constructors.  Each injects the expected value(s) as public
;; variables and asserts equality with the given value(s); the asserts always
;; hold, so the result is the output ID of the given value(s).

; snarkVM circuit/program/src/response/mod.rs: OutputID::constant.
(define crypto-make-output-id-constant ((expected-hash fieldp))
  :returns (id crypto-output-idp)
  (crypto-output-id-constant expected-hash))

; snarkVM circuit/program/src/response/mod.rs: OutputID::public.
(define crypto-make-output-id-public ((expected-hash fieldp))
  :returns (id crypto-output-idp)
  (crypto-output-id-public expected-hash))

; snarkVM circuit/program/src/response/mod.rs: OutputID::private.
(define crypto-make-output-id-private ((expected-hash fieldp))
  :returns (id crypto-output-idp)
  (crypto-output-id-private expected-hash))

; snarkVM circuit/program/src/response/mod.rs: OutputID::record.
; The injected sender ciphertext must equal the expected one or be zero; since
; it is injected from the expected value, the assertion always holds.
(define crypto-make-output-id-record ((expected-commitment fieldp)
                                      (expected-checksum fieldp)
                                      (expected-sender-ciphertext fieldp))
  :returns (id crypto-output-idp)
  (crypto-output-id-record expected-commitment
                           expected-checksum
                           expected-sender-ciphertext))

; snarkVM circuit/program/src/response/mod.rs: OutputID::external_record.
(define crypto-make-output-id-external-record ((expected-hash fieldp))
  :returns (id crypto-output-idp)
  (crypto-output-id-external-record expected-hash))

; snarkVM circuit/program/src/response/mod.rs: OutputID::future.
(define crypto-make-output-id-future ((expected-hash fieldp))
  :returns (id crypto-output-idp)
  (crypto-output-id-future expected-hash))

; snarkVM circuit/program/src/response/mod.rs: OutputID::dynamic_record.
(define crypto-make-output-id-dynamic-record ((expected-hash fieldp))
  :returns (id crypto-output-idp)
  (crypto-output-id-dynamic-record expected-hash))

; snarkVM circuit/program/src/response/mod.rs: OutputID::dynamic_future.
(define crypto-make-output-id-dynamic-future ((expected-hash fieldp))
  :returns (id crypto-output-idp)
  (crypto-output-id-dynamic-future expected-hash))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Hash-based output IDs (shared by from_outputs and process_outputs_from_callback).

; HashPSD8(function_id || output.to_fields() || key || output index), where key
; is tcm (constant, public, future, dynamic future) or tvk (external record,
; dynamic record).  The output must have the given value kind.
(define crypto-output-hash ((function-id fieldp)
                            (output valuep)
                            (key fieldp)
                            (index natp)
                            (kind keywordp))
  :returns (h (implies (not (reserrp h)) (fieldp h)))
  (b* (((fty::ok fields) (crypto-value-to-fields output))
       ((unless (equal (value-kind output) kind)) (spec-error)))
    (crypto-hash-psd 8 (append (list function-id)
                               fields
                               (list key (crypto-index-field index)))))
  :verify-guards nil)

; The ciphertext hash of a private output:
; HashPSD8(output.encrypt_symmetric(HashPSD4(function_id, tvk, index)).to_fields()).
(define crypto-output-private-hash ((function-id fieldp)
                                    (output valuep)
                                    (tvk fieldp)
                                    (index natp))
  :returns (h (implies (not (reserrp h)) (fieldp h)))
  (b* ((output-view-key
        (crypto-hash-psd 4 (list function-id tvk (crypto-index-field index))))
       ((unless (value-case output :plaintext)) (spec-error))
       ((fty::ok ciphertext) (crypto-plaintext-encrypt-symmetric
                         (value-plaintext->get output) output-view-key)))
    (crypto-hash-psd 8 ciphertext))
  :verify-guards nil)

; The output ID of a non-record output (shared by both response functions).
; Errors if the output type is a record type.
(define crypto-output-id-non-record ((function-id fieldp)
                                     (output valuep)
                                     (output-type crypto-value-typep)
                                     (tvk fieldp)
                                     (tcm fieldp)
                                     (index natp))
  :returns (id crypto-output-id-resultp)
  (crypto-value-type-case
   output-type
   :constant (b* (((fty::ok h) (crypto-output-hash function-id output tcm index :plaintext)))
               (crypto-make-output-id-constant h))
   :public (b* (((fty::ok h) (crypto-output-hash function-id output tcm index :plaintext)))
             (crypto-make-output-id-public h))
   :private (b* (((fty::ok h) (crypto-output-private-hash function-id output tvk index)))
              (crypto-make-output-id-private h))
   :record (spec-error)
   :external-record (b* (((fty::ok h) (crypto-output-hash function-id output tvk index :record)))
                      (crypto-make-output-id-external-record h))
   :future (b* (((fty::ok h) (crypto-output-hash function-id output tcm index :future)))
             (crypto-make-output-id-future h))
   :dynamic-record (b* (((fty::ok h) (crypto-output-hash function-id output tvk index
                                                    :dynamic-record)))
                     (crypto-make-output-id-dynamic-record h))
   :dynamic-future (b* (((fty::ok h) (crypto-output-hash function-id output tcm index
                                                    :dynamic-future)))
                     (crypto-make-output-id-dynamic-future h)))
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Response::from_outputs.

; The output ID of a record output in from_outputs: randomizer =
; HashToScalarPSD2(tvk, locator); (encrypted, rvk) = record.encrypt_symmetric(randomizer);
; commitment = record.to_commitment(program_id, name, rvk);
; checksum = HashBHP1024(encrypted.to_bits_le());
; sender_ciphertext = signer.x + HashPSD4(encryption_domain, rvk, 1).
(define crypto-output-id-record-from-output ((signer groupp)
                                             (program-id program-idp)
                                             (record-name identifierp)
                                             (tvk fieldp)
                                             (output valuep)
                                             register)
  :guard (or (null register) (unsigned-byte-p 64 register))
  :returns (id crypto-output-id-resultp)
  (b* (((unless (value-case output :record)) (spec-error))
       (record (value-record->get output))
       ((unless register) (spec-error))
       (randomizer (crypto-hash-to-scalar-psd 2 (list tvk register)))
       ((fty::ok (list encrypted record-view-key))
        (crypto-record-encrypt-symmetric record randomizer))
       ((fty::ok commitment)
        (crypto-record-to-commitment record program-id record-name record-view-key))
       ((fty::ok encrypted-bits) (crypto-ciphertext-record-write-bits-le encrypted))
       (checksum (crypto-hash-bhp 1024 encrypted-bits))
       (sender-randomizer
        (crypto-hash-psd 4 (list (crypto-encryption-domain) record-view-key 1)))
       (sender-ciphertext
        (crypto-field-add (crypto-group-x signer) sender-randomizer)))
    (crypto-make-output-id-record commitment checksum sender-ciphertext))
  :verify-guards nil)

(define crypto-response-from-outputs-loop ((signer groupp)
                                           (program-id program-idp)
                                           (function-id fieldp)
                                           (index natp)
                                           (tvk fieldp)
                                           (tcm fieldp)
                                           (outputs crypto-value-listp)
                                           (output-types crypto-value-type-listp)
                                           (output-registers
                                            crypto-output-register-listp))
  :returns (ids (implies (not (reserrp ids)) (crypto-output-id-listp ids)))
  :measure (len outputs)
  (b* (((when (endp outputs)) nil)
       (output (car outputs))
       (output-type (car output-types))
       ((fty::ok id)
        (if (crypto-value-type-case output-type :record)
            (crypto-output-id-record-from-output
             signer program-id (crypto-value-type-record->name output-type)
             tvk output (car output-registers))
          (crypto-output-id-non-record function-id output output-type
                                       tvk tcm index)))
       ((fty::ok ids) (crypto-response-from-outputs-loop
                  signer program-id function-id (1+ (lnfix index)) tvk tcm
                  (cdr outputs) (cdr output-types) (cdr output-registers))))
    (cons id ids))
  :verify-guards nil)

; snarkVM circuit/program/src/response/from_outputs.rs: Response::from_outputs.
; Output i has index (num_inputs + i) mod 2^16 (as a u16 field); a record
; output uses its register locator instead and halts if it has no register.
; Halts if the numbers of outputs, output types, and output registers differ
; (zip_eq), or an output does not match its output type.
(define crypto-response-from-outputs ((signer groupp)
                                      (network-id acl2::ubyte16p)
                                      (program-id program-idp)
                                      (function-name identifierp)
                                      (num-inputs natp)
                                      (tvk fieldp)
                                      (tcm fieldp)
                                      (outputs crypto-value-listp)
                                      (output-types crypto-value-type-listp)
                                      (output-registers
                                       crypto-output-register-listp))
  :returns (r crypto-response-resultp)
  (b* ((function-id (crypto-compute-function-id network-id program-id function-name))
       ((unless (and (equal (len outputs) (len output-types))
                     (equal (len output-types) (len output-registers))))
        (spec-error))
       ((fty::ok output-ids)
        (crypto-response-from-outputs-loop signer program-id function-id
                                           (lnfix num-inputs) tvk tcm
                                           outputs output-types output-registers)))
    (make-crypto-response :output-ids output-ids :outputs outputs))
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Response::process_outputs_from_callback.

; The output ID of a record output in process_outputs_from_callback:
; randomizer = HashToScalarPSD2(tvk, locator); rvk = (owner * randomizer).x;
; the ID is OutputID::external_record(record.to_commitment(program_id, name, rvk)).
(define crypto-output-id-record-from-callback ((program-id program-idp)
                                               (record-name identifierp)
                                               (tvk fieldp)
                                               (output valuep)
                                               register)
  :guard (or (null register) (unsigned-byte-p 64 register))
  :returns (id crypto-output-id-resultp)
  (b* (((unless (value-case output :record)) (spec-error))
       (record (value-record->get output))
       ((unless register) (spec-error))
       (randomizer (crypto-hash-to-scalar-psd 2 (list tvk register)))
       (record-view-key
        (crypto-group-x (ecurve::edwards-bls12-mul
                         randomizer (crypto-owner-address (record->owner record)))))
       ((fty::ok commitment)
        (crypto-record-to-commitment record program-id record-name record-view-key)))
    (crypto-make-output-id-external-record commitment))
  :verify-guards nil)

(define crypto-process-outputs-from-callback-loop ((program-id program-idp)
                                                   (function-id fieldp)
                                                   (index natp)
                                                   (tvk fieldp)
                                                   (tcm fieldp)
                                                   (outputs crypto-value-listp)
                                                   (output-types
                                                    crypto-value-type-listp)
                                                   (output-registers
                                                    crypto-output-register-listp))
  :returns (ids (implies (not (reserrp ids)) (crypto-output-id-listp ids)))
  :measure (len outputs)
  (b* (((when (endp outputs)) nil)
       (output (car outputs))
       (output-type (car output-types))
       ((fty::ok id)
        (if (crypto-value-type-case output-type :record)
            (crypto-output-id-record-from-callback
             program-id (crypto-value-type-record->name output-type)
             tvk output (car output-registers))
          (crypto-output-id-non-record function-id output output-type
                                       tvk tcm index)))
       ((fty::ok ids) (crypto-process-outputs-from-callback-loop
                  program-id function-id (1+ (lnfix index)) tvk tcm
                  (cdr outputs) (cdr output-types) (cdr output-registers))))
    (cons id ids))
  :verify-guards nil)

; snarkVM circuit/program/src/response/process_outputs_from_callback.rs:
; Response::process_outputs_from_callback.  Injects the (console) outputs and
; returns them; the output IDs are computed (as in from_outputs, except that a
; record output yields an external record ID of its commitment, with the record
; view key derived from the owner) only for their halting behavior.
; function-id nil means None, in which case it is computed.
(define crypto-response-process-outputs-from-callback
  ((network-id acl2::ubyte16p)
   (program-id program-idp)
   (function-name identifierp)
   (num-inputs natp)
   (tvk fieldp)
   (tcm fieldp)
   (outputs crypto-value-listp)
   (output-types crypto-value-type-listp)
   (output-registers crypto-output-register-listp)
   (function-id crypto-maybe-fieldp))
  :returns (r crypto-value-list-resultp)
  (b* ((function-id (or function-id
                        (crypto-compute-function-id network-id program-id
                                                    function-name)))
       ((unless (and (equal (len outputs) (len output-types))
                     (equal (len output-types) (len output-registers))))
        (spec-error))
       ((fty::ok &)
        (crypto-process-outputs-from-callback-loop program-id function-id
                                                   (lnfix num-inputs) tvk tcm
                                                   outputs output-types
                                                   output-registers)))
    (crypto-value-list-fix outputs))
  :verify-guards nil)
