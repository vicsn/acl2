; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specifications of snarkVM's circuit InputID and Request
; (circuit/program/src/request).

(in-package "ALEOVM")

(include-book "crypto-record")

(local (include-book "arithmetic-5/top" :dir :system))

(local (in-theory (disable bitp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types.

; snarkVM circuit/program/src/request/mod.rs: enum InputID.
(fty::deftagsum crypto-input-id
  (:constant ((hash values-field)))
  (:public ((hash values-field)))
  (:private ((hash values-field)))
  (:record ((commitment values-field)
            (gamma values-group)
            (record-view-key values-field)
            (serial-number values-field)
            (tag values-field)))
  (:external-record ((hash values-field)))
  (:dynamic-record ((hash values-field)))
  :pred crypto-input-idp)

(fty::deflist crypto-input-id-list
  :elt-type crypto-input-id
  :true-listp t
  :elementp-of-nil nil
  :pred crypto-input-id-listp)

; snarkVM console/program/src/data_types/value_type: enum ValueType.
; Only the record name of ValueType::Record is used by the circuits
; specified here; the other payloads (plaintext types, locators) are omitted.
(fty::deftagsum crypto-value-type
  (:constant ())
  (:public ())
  (:private ())
  (:record ((name identifier)))
  (:external-record ())
  (:future ())
  (:dynamic-record ())
  (:dynamic-future ())
  :pred crypto-value-typep)

(fty::deflist crypto-value-type-list
  :elt-type crypto-value-type
  :true-listp t
  :elementp-of-nil nil
  :pred crypto-value-type-listp)

(fty::deflist crypto-value-list
  :elt-type value
  :true-listp t
  :elementp-of-nil nil
  :pred crypto-value-listp)

; snarkVM circuit/program/src/request/mod.rs: struct Request.
(fty::defprod crypto-request
  ((signer values-group)
   (network-id acl2::ubyte16)
   (program-id program-id)
   (function-name identifier)
   (input-ids crypto-input-id-list)
   (inputs crypto-value-list)
   (signature signature)
   (sk-tag values-field)
   (tvk values-field)
   (tcm values-field)
   (scm values-field)
   (is-dynamic bool))
  :tag :crypto-request
  :pred crypto-requestp)

(fty::defresult crypto-request-result
  :ok crypto-request
  :pred crypto-request-resultp)

(define crypto-maybe-fieldp (x)
  :returns (yes/no booleanp)
  :short "An optional field element (Option<Field>): @('nil') is @('None')."
  (or (null x) (fieldp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Helpers.

; snarkVM circuit/program/src/function_id/mod.rs: compute_function_id =
; HashBHP1024(network_id || name size in bits || name || network size in bits
;             || network || function name size in bits || function name).
(define crypto-compute-function-id ((network-id acl2::ubyte16p)
                                    (program-id program-idp)
                                    (function-name identifierp))
  :returns (id fieldp)
  (b* ((name (program-id->name program-id))
       (network (program-id->network program-id)))
    (crypto-hash-bhp
     1024
     (append (crypto-nat->lebits 16 (acl2::ubyte16-fix network-id))
             (crypto-nat->lebits 8 (crypto-identifier-size-in-bits name))
             (crypto-identifier-bits-le name)
             (crypto-nat->lebits 8 (crypto-identifier-size-in-bits network))
             (crypto-identifier-bits-le network)
             (crypto-nat->lebits 8 (crypto-identifier-size-in-bits function-name))
             (crypto-identifier-bits-le function-name)))))

; snarkVM circuit/account/src/compute_key/from.rs: sk_prf = HashToScalarPSD4(pk_sig.x, pr_sig.x).
(define crypto-compute-key-sk-prf ((pk-sig groupp) (pr-sig groupp))
  :returns (s scalarp)
  (crypto-hash-to-scalar-psd 4 (list (crypto-group-x pk-sig) (crypto-group-x pr-sig))))

; snarkVM circuit/account/src/compute_key/to_address.rs: ComputeKey::to_address
; = pk_sig + pr_sig + sk_prf * G.
(define crypto-compute-key-to-address ((ck compute-keyp))
  :returns (a ecurve::edwards-bls12-pointp)
  (ecurve::edwards-bls12-add
   (ecurve::edwards-bls12-add (compute-key->pk-sig ck) (compute-key->pr-sig ck))
   (crypto-g-scalar-multiply (compute-key->sk-prf ck))))

; The index of an input/output as a field: Field::from_u16(index as u16).
(define crypto-index-field ((index natp))
  :returns (f fieldp
              :hints (("Goal" :in-theory (enable fieldp pfield::fep base-prime
                                                 (:e ecurve::edwards-bls12-q)))))
  (mod (lnfix index) 65536))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; InputID and Request construction.

; snarkVM circuit/program/src/request/mod.rs: InputID::new (Inject).
(define crypto-input-id-new ((input-id crypto-input-idp))
  :returns (id crypto-input-idp)
  (crypto-input-id-fix input-id))

(define crypto-request-inputs-match ((input-ids crypto-input-id-listp)
                                     (inputs crypto-value-listp))
  :returns (yes/no booleanp)
  :short "Each input has the kind required by its input ID."
  (b* (((when (or (endp input-ids) (endp inputs))) t)
       (id (car input-ids))
       (input (car inputs))
       (ok (case (crypto-input-id-kind id)
             ((:constant :public :private) (value-case input :plaintext))
             ((:record :external-record) (value-case input :record))
             (otherwise (value-case input :dynamic-record)))))
    (and ok (crypto-request-inputs-match (cdr input-ids) (cdr inputs)))))

; snarkVM circuit/program/src/request/mod.rs: Request::new (Inject).
; Halts if the numbers of input IDs and inputs differ (zip_eq) or an input
; does not have the kind of its input ID.  The signature's compute key is
; injected with ComputeKey::new, which recomputes sk_prf from pk_sig and pr_sig.
(define crypto-request-new ((request crypto-requestp))
  :returns (r crypto-request-resultp)
  (b* ((input-ids (crypto-request->input-ids request))
       (inputs (crypto-request->inputs request))
       ((unless (equal (len input-ids) (len inputs))) (spec-error))
       ((unless (crypto-request-inputs-match input-ids inputs)) (spec-error))
       (signature (crypto-request->signature request))
       (ck (signature->compute-key signature))
       (ck (change-compute-key ck :sk-prf (crypto-compute-key-sk-prf
                                           (compute-key->pk-sig ck)
                                           (compute-key->pr-sig ck))))
       (signature (change-signature signature :compute-key ck)))
    (change-crypto-request request :signature signature)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Transition public key.

; snarkVM circuit/program/src/request/to_tpk.rs: Request::to_tpk
; = challenge * pk_sig + response * G.
(define crypto-request-to-tpk ((request crypto-requestp))
  :returns (tpk ecurve::edwards-bls12-pointp)
  (b* ((signature (crypto-request->signature request))
       (pk-sig (compute-key->pk-sig (signature->compute-key signature))))
    (ecurve::edwards-bls12-add
     (ecurve::edwards-bls12-mul (signature->challenge signature) pk-sig)
     (crypto-g-scalar-multiply (signature->response signature)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Input ID checks.

; The check of one input against its input ID, in check_input_ids.
; Returns (list check message-elements), where the message elements are
; those appended when CREATE_MESSAGE is set.
(define crypto-check-input-id ((create-message booleanp)
                               (index natp)
                               (input-id crypto-input-idp)
                               (input valuep)
                               (input-type crypto-value-typep)
                               (function-id fieldp)
                               (program-id program-idp)
                               (signer groupp)
                               (sk-tag fieldp)
                               (tvk fieldp)
                               (tcm fieldp)
                               signature)
  :guard (or (null signature) (signaturep signature))
  :returns (res (implies (not (reserrp res)) (true-listp res)))
  (b* ((input-index (crypto-index-field index)))
    (crypto-input-id-case
     input-id
     ;; A constant or public input is hashed (using tcm) to a field element.
     :constant
     (b* (((fty::ok fields) (crypto-value-to-fields input))
          (preimage (append (list function-id) fields (list tcm input-index)))
          ((unless (value-case input :plaintext)) (spec-error)))
       (list (crypto-bit-eq input-id.hash (crypto-hash-psd 8 preimage))
             (and create-message (list input-id.hash))))
     :public
     (b* (((fty::ok fields) (crypto-value-to-fields input))
          (preimage (append (list function-id) fields (list tcm input-index)))
          ((unless (value-case input :plaintext)) (spec-error)))
       (list (crypto-bit-eq input-id.hash (crypto-hash-psd 8 preimage))
             (and create-message (list input-id.hash))))
     ;; A private input is encrypted (using tvk) and the ciphertext is hashed.
     :private
     (b* ((input-view-key (crypto-hash-psd 4 (list function-id tvk input-index)))
          ((unless (value-case input :plaintext)) (spec-error))
          ((fty::ok ciphertext) (crypto-plaintext-encrypt-symmetric
                            (value-plaintext->get input) input-view-key)))
       (list (crypto-bit-eq input-id.hash (crypto-hash-psd 8 ciphertext))
             (and create-message (list input-id.hash))))
     ;; A record input: commitment, serial number, tag, and owner checks.
     :record
     (b* (((unless (value-case input :record)) (spec-error))
          (record (value-record->get input))
          ((unless (crypto-value-type-case input-type :record)) (spec-error))
          (record-name (crypto-value-type-record->name input-type))
          ((fty::ok candidate-commitment)
           (crypto-record-to-commitment record program-id record-name
                                        input-id.record-view-key))
          (candidate-serial-number
           (crypto-record-serial-number-from-gamma input-id.gamma
                                                   candidate-commitment))
          (candidate-tag (crypto-record-tag sk-tag candidate-commitment))
          ((fty::ok message)
           (if create-message
               (b* (((unless signature) (spec-error))
                    (challenge (signature->challenge signature))
                    (response (signature->response signature))
                    ((fty::ok h) (crypto-hash-to-group-psd
                             2 (list (crypto-serial-number-domain)
                                     candidate-commitment)))
                    (h-r (ecurve::edwards-bls12-add
                          (ecurve::edwards-bls12-mul challenge input-id.gamma)
                          (ecurve::edwards-bls12-mul response h))))
                 (list (crypto-group-x h)
                       (crypto-group-x h-r)
                       (crypto-group-x input-id.gamma)
                       candidate-tag))
             nil)))
       (list (crypto-bit-and
              (crypto-bit-and
               (crypto-bit-and
                (crypto-bit-eq input-id.serial-number candidate-serial-number)
                (crypto-bit-eq input-id.commitment candidate-commitment))
               (crypto-bit-eq input-id.tag candidate-tag))
              (crypto-bit-eq (crypto-owner-address (record->owner record))
                             signer))
             message))
     ;; An external record input is hashed (using tvk) to a field element.
     :external-record
     (b* (((unless (value-case input :record)) (spec-error))
          ((fty::ok fields) (crypto-record-to-fields (value-record->get input)))
          (preimage (append (list function-id) fields (list tvk input-index))))
       (list (crypto-bit-eq input-id.hash (crypto-hash-psd 8 preimage))
             (and create-message (list input-id.hash))))
     ;; A dynamic record input is hashed (using tvk) to a field element.
     :dynamic-record
     (b* (((unless (value-case input :dynamic-record)) (spec-error))
          ((fty::ok fields) (crypto-bits-to-fields-checked
                        (crypto-dynamic-record-bits-le
                         (value-dynamic-record->get input))))
          (preimage (append (list function-id) fields (list tvk input-index))))
       (list (crypto-bit-eq input-id.hash (crypto-hash-psd 8 preimage))
             (and create-message (list input-id.hash))))))
  :verify-guards nil)

(define crypto-check-input-ids-loop ((create-message booleanp)
                                     (index natp)
                                     (input-ids crypto-input-id-listp)
                                     (inputs crypto-value-listp)
                                     (input-types crypto-value-type-listp)
                                     (function-id fieldp)
                                     (program-id program-idp)
                                     (signer groupp)
                                     (sk-tag fieldp)
                                     (tvk fieldp)
                                     (tcm fieldp)
                                     signature)
  :guard (or (null signature) (signaturep signature))
  :returns (res (implies (not (reserrp res)) (true-listp res)))
  :measure (len input-ids)
  (b* (((when (endp input-ids)) (list 1 nil))
       ((fty::ok (list check message))
        (crypto-check-input-id create-message index (car input-ids) (car inputs)
                               (car input-types) function-id program-id signer
                               sk-tag tvk tcm signature))
       ((fty::ok (list checks messages))
        (crypto-check-input-ids-loop create-message (1+ (lnfix index))
                                     (cdr input-ids) (cdr inputs) (cdr input-types)
                                     function-id program-id signer
                                     sk-tag tvk tcm signature)))
    (list (crypto-bit-and check checks)
          (append message messages)))
  :verify-guards nil)

; snarkVM circuit/program/src/request/verify.rs: Request::check_input_ids::<CREATE_MESSAGE>.
; Returns (list checks message), where checks is the conjunction of the input
; checks and message is the list of message elements if CREATE_MESSAGE
; (Some(message)), nil otherwise (None).  The signature is nil for None and must
; be present exactly when CREATE_MESSAGE; function-id nil means None, in which
; case the function ID is computed.  The input IDs, inputs, and input types
; must have the same length (zip_eq).
(define crypto-request-check-input-ids ((create-message booleanp)
                                        (network-id acl2::ubyte16p)
                                        (program-id program-idp)
                                        (function-name identifierp)
                                        (input-ids crypto-input-id-listp)
                                        (inputs crypto-value-listp)
                                        (input-types crypto-value-type-listp)
                                        (signer groupp)
                                        (sk-tag fieldp)
                                        (tvk fieldp)
                                        (tcm fieldp)
                                        signature
                                        (function-id crypto-maybe-fieldp))
  :guard (or (null signature) (signaturep signature))
  :returns (res (implies (not (reserrp res)) (true-listp res)))
  (b* (((unless (iff create-message signature)) (spec-error))
       (function-id (or function-id
                        (crypto-compute-function-id network-id program-id
                                                    function-name)))
       ((unless (and (equal (len input-ids) (len inputs))
                     (equal (len inputs) (len input-types))))
        (spec-error)))
    (crypto-check-input-ids-loop create-message 0 input-ids inputs input-types
                                 function-id program-id signer sk-tag tvk tcm
                                 signature))
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Request verification.

; snarkVM circuit/program/src/request/verify.rs: Request::verify.
; root-tvk and program-checksum are optional fields (nil = None).
; The result is the conjunction of
;   signature checks: challenge = HashToScalarPSD8(tpk.x, pk_sig.x, pr_sig.x,
;     signer.x, message) and signer = compute_key.to_address(), where
;     message = [tvk, tcm, function ID, is_root, program checksum?, input elements];
;   input checks (check_input_ids::<true>);
;   tpk checks: tpk = to_tpk(), tcm = HashPSD2(tvk), and
;     scm = HashPSD2(signer.x, root_tvk), with root_tvk defaulting to tvk.
(define crypto-request-verify ((request crypto-requestp)
                               (input-types crypto-value-type-listp)
                               (tpk ecurve::edwards-bls12-pointp)
                               (root-tvk crypto-maybe-fieldp)
                               (is-root bitp)
                               (program-checksum crypto-maybe-fieldp))
  :returns (r (implies (not (reserrp r)) (bitp r)))
  (b* (((crypto-request request) request)
       (function-id (crypto-compute-function-id request.network-id
                                                request.program-id
                                                request.function-name))
       (is-root-field (if (equal is-root 1) 1 0))
       (message (append (list request.tvk request.tcm function-id is-root-field)
                        (and program-checksum (list program-checksum))))
       ((fty::ok (list input-checks input-message))
        (crypto-request-check-input-ids t
                                        request.network-id
                                        request.program-id
                                        request.function-name
                                        request.input-ids
                                        request.inputs
                                        input-types
                                        request.signer
                                        request.sk-tag
                                        request.tvk
                                        request.tcm
                                        request.signature
                                        nil))
       (message (append message input-message))
       (root-tvk (or root-tvk request.tvk))
       (tpk-checks
        (crypto-bit-and
         (crypto-bit-and
          (crypto-bit-eq tpk (crypto-request-to-tpk request))
          (crypto-bit-eq (crypto-hash-psd 2 (list request.tvk)) request.tcm))
         (crypto-bit-eq (crypto-hash-psd 2 (list (crypto-group-x request.signer)
                                                 root-tvk))
                        request.scm)))
       (ck (signature->compute-key request.signature))
       (preimage (append (list (crypto-group-x tpk)
                               (crypto-group-x (compute-key->pk-sig ck))
                               (crypto-group-x (compute-key->pr-sig ck))
                               (crypto-group-x request.signer))
                         message))
       (candidate-challenge (crypto-hash-to-scalar-psd 8 preimage))
       (candidate-address (crypto-compute-key-to-address ck))
       (signature-checks
        (crypto-bit-and
         (crypto-bit-eq (signature->challenge request.signature) candidate-challenge)
         (crypto-bit-eq request.signer candidate-address))))
    (crypto-bit-and (crypto-bit-and signature-checks input-checks) tpk-checks))
  :verify-guards nil)
