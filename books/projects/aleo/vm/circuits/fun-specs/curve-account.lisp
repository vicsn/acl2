; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specifications of the constraint-generating functions
; of snarkVM's circuit/account crate
; (PrivateKey, ComputeKey, ViewKey, Signature).
;
; Values:
;   - A private key is its two scalars (sk_sig, r_sig).
;   - A compute key is the list (pk_sig pr_sig sk_prf) of
;     two group values and a scalar.
;   - A view key is a scalar.
;   - A signature is the list (challenge response compute-key).
;   - An address is a group value (see curve-address.lisp).
; See curve-group.lisp for the conventions of the curve-* books.

(in-package "ALEOVM")

(include-book "curve-address")
(include-book "curve-network")

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(local (in-theory (e/d (spec-error curve-not-reserrp-when-pointp)
                        (bitp (:e base-prime) (:e scalar-prime)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Values.

(define curve-compute-keyp (x)
  :returns (yes/no booleanp)
  :short "A compute key @('(pk_sig pr_sig sk_prf)')."
  (and (true-listp x)
       (equal (len x) 3)
       (ecurve::edwards-bls12-pointp (first x))
       (ecurve::edwards-bls12-pointp (second x))
       (scalarp (third x)))
  ///
  (defrule curve-compute-keyp-forward
    (implies (curve-compute-keyp x)
             (and (ecurve::edwards-bls12-pointp (first x))
                  (ecurve::edwards-bls12-pointp (second x))
                  (scalarp (third x))))
    :rule-classes (:rewrite :forward-chaining))
  (defrule curve-compute-keyp-of-list
    (equal (curve-compute-keyp (list pk-sig pr-sig sk-prf))
           (and (ecurve::edwards-bls12-pointp pk-sig)
                (ecurve::edwards-bls12-pointp pr-sig)
                (scalarp sk-prf)))))

(define curve-signaturep (x)
  :returns (yes/no booleanp)
  :short "A signature @('(challenge response compute-key)')."
  (and (true-listp x)
       (equal (len x) 3)
       (scalarp (first x))
       (scalarp (second x))
       (curve-compute-keyp (third x)))
  ///
  (defrule curve-signaturep-forward
    (implies (curve-signaturep x)
             (and (scalarp (first x))
                  (scalarp (second x))
                  (curve-compute-keyp (third x))))
    :rule-classes (:rewrite :forward-chaining))
  (defrule curve-signaturep-of-list
    (equal (curve-signaturep (list challenge response compute-key))
           (and (scalarp challenge)
                (scalarp response)
                (curve-compute-keyp compute-key)))))

(define curve-scalar-add ((s1 scalarp) (s2 scalarp))
  :returns (s scalarp)
  :short "Scalar addition, modulo the subgroup order."
  (pfield::add s1 s2 (scalar-prime))
  :guard-hints (("Goal" :in-theory (enable pfield::fep))))

(defrule curve-fieldp-when-scalarp
  (implies (scalarp s)
           (fieldp s))
  :enable (pfield::fep)
  :use curve-scalar-prime-below-base-prime
  :prep-lemmas
  ((defrule curve-scalar-prime-below-base-prime
     (< (scalar-prime) (base-prime))
     :enable (scalar-prime base-prime ecurve::edwards-bls12-r
                           ecurve::edwards-bls12-q))))

(defrule curve-fep-base-prime-when-scalarp
  (implies (scalarp s)
           (pfield::fep s (base-prime)))
  :enable (fieldp)
  :use curve-fieldp-when-scalarp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Compute keys.

; snarkVM circuit/account/src/compute_key/from.rs: From<(Group, Group)>::from
(define compute-key-from-funspec ((pk-sig ecurve::edwards-bls12-pointp)
                                  (pr-sig ecurve::edwards-bls12-pointp))
  :returns (ck curve-compute-keyp :hyp :guard)
  :short "@('sk_prf := HashToScalar_psd4(pk_sig.x, pr_sig.x)')."
  (list pk-sig
        pr-sig
        (aleo-hash-to-scalar-psd4-funspec
         (list (ecurve::point-finite->x pk-sig)
               (ecurve::point-finite->x pr-sig))))
  :guard-hints (("Goal" :in-theory (enable pfield::fe-listp))))

; snarkVM circuit/account/src/compute_key/from_private_key.rs: ComputeKey::from_private_key
(define compute-key-from-private-key-funspec ((sk-sig scalarp) (r-sig scalarp))
  :returns (ck curve-compute-keyp)
  :short "@('pk_sig := sk_sig G'), @('pr_sig := r_sig G'),
          and @('sk_prf') from them as in @(tsee compute-key-from-funspec)."
  (compute-key-from-funspec (aleo-g-scalar-multiply-funspec sk-sig)
                            (aleo-g-scalar-multiply-funspec r-sig)))

; snarkVM circuit/account/src/compute_key/to_address.rs: ComputeKey::to_address
(define compute-key-to-address-funspec ((ck curve-compute-keyp))
  :returns (address ecurve::edwards-bls12-pointp)
  :short "@('pk_sig + pr_sig + sk_prf G')."
  (b* (((list pk-sig pr-sig sk-prf) ck)
       ((unless (mbt (curve-compute-keyp ck))) (ecurve::twisted-edwards-zero)))
    (group-add-funspec (group-add-funspec pk-sig pr-sig)
                       (aleo-g-scalar-multiply-funspec sk-prf))))

; snarkVM circuit/account/src/compute_key/mod.rs: Inject::new
(define compute-key-new-funspec (pk-sig pr-sig)
  :returns (res (implies (not (reserrp res)) (curve-compute-keyp res)))
  :short "Inject @('pk_sig') and @('pr_sig') (enforced in the subgroup),
          then derive @('sk_prf') as in @(tsee compute-key-from-funspec)."
  (b* ((pk-sig (group-new-funspec pk-sig))
       ((when (reserrp pk-sig)) pk-sig)
       (pr-sig (group-new-funspec pr-sig))
       ((when (reserrp pr-sig)) pr-sig))
    (compute-key-from-funspec pk-sig pr-sig))
  :guard-hints (("Goal" :in-theory (enable groupp))))

; snarkVM circuit/account/src/compute_key/equal.rs: Equal::is_equal
(define compute-key-is-equal-funspec ((ck1 curve-compute-keyp) (ck2 curve-compute-keyp))
  :returns (b bitp)
  :short "@('pk_sig'), @('pr_sig') and @('sk_prf') are pairwise equal."
  (if (equal ck1 ck2) 1 0))

; snarkVM circuit/account/src/compute_key/equal.rs: Equal::is_not_equal
(define compute-key-is-not-equal-funspec ((ck1 curve-compute-keyp) (ck2 curve-compute-keyp))
  :returns (b bitp)
  (if (equal ck1 ck2) 0 1))

; snarkVM circuit/account/src/compute_key/ternary.rs: Ternary::ternary
(define compute-key-ternary-funspec ((c bitp) ck1 ck2)
  :short "Component-wise selection, i.e. @('ck1') if the condition is 1, else @('ck2')."
  (if (equal c 1) ck1 ck2))

; snarkVM circuit/account/src/compute_key/helpers/from_bits.rs: FromBits::from_bits_le
(define compute-key-from-bits-le-funspec ((bits bit-listp))
  :returns (res (implies (not (reserrp res)) (curve-compute-keyp res)))
  :short "Halts on fewer than 506 bits; bits 0-252 and 253-505 are the
          x-coordinates of @('pk_sig') and @('pr_sig') (via @('Group::from_bits_le'));
          later bits are ignored."
  (b* (((when (< (len bits) 506)) (spec-error))
       (pk-sig (group-from-bits-le-funspec (take 253 bits)))
       ((when (reserrp pk-sig)) pk-sig)
       (pr-sig (group-from-bits-le-funspec (take 253 (nthcdr 253 bits))))
       ((when (reserrp pr-sig)) pr-sig))
    (compute-key-from-funspec pk-sig pr-sig))
  :guard-hints (("Goal" :in-theory (enable groupp))))

; snarkVM circuit/account/src/compute_key/helpers/from_bits.rs: FromBits::from_bits_be
(define compute-key-from-bits-be-funspec ((bits bit-listp))
  :returns (res (implies (not (reserrp res)) (curve-compute-keyp res)))
  :short "As @(tsee compute-key-from-bits-le-funspec),
          with each 253-bit chunk big-endian."
  (b* (((when (< (len bits) 506)) (spec-error))
       (pk-sig (group-from-bits-be-funspec (take 253 bits)))
       ((when (reserrp pk-sig)) pk-sig)
       (pr-sig (group-from-bits-be-funspec (take 253 (nthcdr 253 bits))))
       ((when (reserrp pr-sig)) pr-sig))
    (compute-key-from-funspec pk-sig pr-sig))
  :guard-hints (("Goal" :in-theory (enable groupp))))

; snarkVM circuit/account/src/compute_key/helpers/to_bits.rs: ToBits::write_bits_le
(define compute-key-write-bits-le-funspec ((ck curve-compute-keyp))
  :returns (bits bit-listp)
  :short "The bits of @('pk_sig') then @('pr_sig') (253 each); @('sk_prf') is not written."
  (append (group-write-bits-le-funspec (first ck))
          (group-write-bits-le-funspec (second ck))))

; snarkVM circuit/account/src/compute_key/helpers/to_bits.rs: ToBits::write_bits_be
(define compute-key-write-bits-be-funspec ((ck curve-compute-keyp))
  :returns (bits bit-listp)
  (append (group-write-bits-be-funspec (first ck))
          (group-write-bits-be-funspec (second ck))))

; snarkVM circuit/account/src/compute_key/helpers/to_fields.rs: ToFields::to_fields
(define compute-key-to-fields-funspec ((ck curve-compute-keyp))
  :returns (fields (pfield::fe-listp fields (base-prime))
                   :hyp :guard
                   :hints (("Goal" :in-theory (enable pfield::fe-listp))))
  :short "The x-coordinates of @('pk_sig') and @('pr_sig')."
  (list (group-to-x-coordinate-funspec (first ck))
        (group-to-x-coordinate-funspec (second ck))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Private keys and view keys.

; snarkVM circuit/account/src/private_key/to_compute_key.rs: PrivateKey::to_compute_key
(define private-key-to-compute-key-funspec ((sk-sig scalarp) (r-sig scalarp))
  :returns (ck curve-compute-keyp)
  (compute-key-from-private-key-funspec sk-sig r-sig))

; snarkVM circuit/account/src/view_key/from_private_key.rs: ViewKey::from_private_key
(define view-key-from-private-key-funspec ((sk-sig scalarp) (r-sig scalarp))
  :returns (vk scalarp)
  :short "@('sk_sig + r_sig + sk_prf') (scalar addition),
          with @('sk_prf') from the compute key."
  (b* ((ck (private-key-to-compute-key-funspec sk-sig r-sig)))
    (curve-scalar-add (curve-scalar-add sk-sig r-sig) (third ck))))

; snarkVM circuit/account/src/private_key/to_view_key.rs: PrivateKey::to_view_key
(define private-key-to-view-key-funspec ((sk-sig scalarp) (r-sig scalarp))
  :returns (vk scalarp)
  (view-key-from-private-key-funspec sk-sig r-sig))

; snarkVM circuit/account/src/view_key/to_address.rs: ViewKey::to_address
(define view-key-to-address-funspec ((vk scalarp))
  :returns (address ecurve::edwards-bls12-pointp)
  :short "@('view_key G')."
  (aleo-g-scalar-multiply-funspec vk))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Signatures.

; snarkVM circuit/account/src/signature/verify.rs: Signature::verify
(define signature-verify-funspec ((sig curve-signaturep)
                                  (address ecurve::edwards-bls12-pointp)
                                  (message (pfield::fe-listp message (base-prime))))
  :returns (b bitp)
  :short "With @('g_nonce := response G + challenge pk_sig'):
          1 iff @('challenge') is
          @('HashToScalar_psd8(g_nonce.x, pk_sig.x, pr_sig.x, address.x, message...)')
          and @('address') is the compute key's address."
  (b* (((list challenge response ck) sig)
       ((list pk-sig pr-sig &) ck)
       ((unless (mbt (curve-signaturep sig))) 0)
       (g-nonce (group-add-funspec (aleo-g-scalar-multiply-funspec response)
                                   (group-mul-funspec pk-sig challenge)))
       (preimage (list* (ecurve::point-finite->x g-nonce)
                        (ecurve::point-finite->x pk-sig)
                        (ecurve::point-finite->x pr-sig)
                        (address-to-field-funspec address)
                        message))
       (candidate-challenge (aleo-hash-to-scalar-psd8-funspec preimage))
       (candidate-address (compute-key-to-address-funspec ck)))
    (if (and (equal challenge candidate-challenge)
             (equal address candidate-address))
        1
      0)))

; snarkVM circuit/account/src/signature/mod.rs: Inject::new
(define signature-new-funspec ((challenge scalarp) (response scalarp) pk-sig pr-sig)
  :returns (res (implies (not (reserrp res)) (curve-signaturep res))
                :hyp (and (scalarp challenge) (scalarp response)))
  :short "Inject the scalars (always valid) and the compute key
          (as @(tsee compute-key-new-funspec))."
  (b* ((ck (compute-key-new-funspec pk-sig pr-sig))
       ((when (reserrp ck)) ck))
    (list challenge response ck)))

; snarkVM circuit/account/src/signature/equal.rs: Equal::is_equal
(define signature-is-equal-funspec ((sig1 curve-signaturep) (sig2 curve-signaturep))
  :returns (b bitp)
  :short "Challenge, response and compute key are pairwise equal."
  (if (equal sig1 sig2) 1 0))

; snarkVM circuit/account/src/signature/equal.rs: Equal::is_not_equal
(define signature-is-not-equal-funspec ((sig1 curve-signaturep) (sig2 curve-signaturep))
  :returns (b bitp)
  (if (equal sig1 sig2) 0 1))

; snarkVM circuit/account/src/signature/ternary.rs: Ternary::ternary
(define signature-ternary-funspec ((c bitp) sig1 sig2)
  :short "Component-wise selection, i.e. @('sig1') if the condition is 1, else @('sig2')."
  (if (equal c 1) sig1 sig2))

; snarkVM circuit/account/src/signature/helpers/from_bits.rs: FromBits::from_bits_le
(define signature-from-bits-le-funspec ((bits bit-listp))
  :returns (res (implies (not (reserrp res)) (curve-signaturep res)))
  :short "Halts on fewer than 1008 bits; bits 0-250 are the challenge,
          251-501 the response (@('Scalar::from_bits_le'))
          and 502-1007 the compute key (@('ComputeKey::from_bits_le'));
          later bits are ignored."
  (b* (((when (< (len bits) 1008)) (spec-error))
       (challenge (curve-scalar-from-bits-le (take 251 bits)))
       ((when (reserrp challenge)) challenge)
       (response (curve-scalar-from-bits-le (take 251 (nthcdr 251 bits))))
       ((when (reserrp response)) response)
       (ck (compute-key-from-bits-le-funspec (take 506 (nthcdr 502 bits))))
       ((when (reserrp ck)) ck))
    (list challenge response ck)))

; snarkVM circuit/account/src/signature/helpers/from_bits.rs: FromBits::from_bits_be
(define signature-from-bits-be-funspec ((bits bit-listp))
  :returns (res (implies (not (reserrp res)) (curve-signaturep res)))
  :short "As @(tsee signature-from-bits-le-funspec), with big-endian components."
  (b* (((when (< (len bits) 1008)) (spec-error))
       (challenge (curve-scalar-from-bits-be (take 251 bits)))
       ((when (reserrp challenge)) challenge)
       (response (curve-scalar-from-bits-be (take 251 (nthcdr 251 bits))))
       ((when (reserrp response)) response)
       (ck (compute-key-from-bits-be-funspec (take 506 (nthcdr 502 bits))))
       ((when (reserrp ck)) ck))
    (list challenge response ck)))

; snarkVM circuit/account/src/signature/helpers/to_bits.rs: ToBits::write_bits_le
(define signature-write-bits-le-funspec ((sig curve-signaturep))
  :returns (bits bit-listp)
  :short "Challenge (251 bits), response (251 bits), compute key (506 bits)."
  (append (curve-scalar-to-bits-le (first sig))
          (curve-scalar-to-bits-le (second sig))
          (compute-key-write-bits-le-funspec (third sig))))

; snarkVM circuit/account/src/signature/helpers/to_bits.rs: ToBits::write_bits_be
(define signature-write-bits-be-funspec ((sig curve-signaturep))
  :returns (bits bit-listp)
  (append (curve-scalar-to-bits-be (first sig))
          (curve-scalar-to-bits-be (second sig))
          (compute-key-write-bits-be-funspec (third sig))))

; snarkVM circuit/account/src/signature/helpers/to_fields.rs: ToFields::to_fields
(define signature-to-fields-funspec ((sig curve-signaturep))
  :returns (fields (pfield::fe-listp fields (base-prime))
                   :hyp :guard
                   :hints (("Goal" :in-theory (enable pfield::fe-listp))))
  :short "Challenge and response as fields, then the compute key's fields."
  (list* (lnfix (first sig))
         (lnfix (second sig))
         (compute-key-to-fields-funspec (third sig))))
