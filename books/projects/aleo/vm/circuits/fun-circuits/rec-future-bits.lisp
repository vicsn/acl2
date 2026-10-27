; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Future::write_bits_le / write_bits_be / to_fields and
; Argument::write_bits_le / write_bits_be
; (snarkVM circuit/program/src/data/future/{to_bits.rs,to_fields.rs,argument.rs}).
;
; The program ID, function name, all length prefixes (U16 / U8 / U32
; constants) and the argument tags are synthesis-time constants; the only
; constraints are those of the plaintext arguments' write_bits and of the
; DynamicFuture arguments' Field::write_bits_le.

(in-package "ALEOVM")

(include-book "rec-future")
(include-book "rec-record-bits")

(local (include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system))
(local (include-book "std/lists/rev" :dir :system))

(set-verify-guards-eagerness 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DynamicFuture leaves.

(define rec-dfbits-out (dfw bigp)
  (if bigp
      (rec-concat-be (rec-dfw-xs dfw) (nth 4 dfw))
    (rec-concat-le (rec-dfw-xs dfw) (nth 4 dfw))))

(define rec-dfbits-gadget (dfw u)
  (rec-dynamic-future-write-bits-gadget (nth 0 dfw) (nth 1 dfw) (nth 2 dfw)
                                        (nth 3 dfw) (nth 4 dfw) (nth 5 dfw) u))

(defruled rec-symbol-listp-of-concat
  (implies (rec-bits-shapep xs bitss rss)
           (and (symbol-listp (rec-concat-le xs bitss))
                (symbol-listp (rec-concat-be xs bitss))))
  :induct (rec-bits-shapep xs bitss rss)
  :enable (rec-bits-shapep rec-concat-le rec-concat-be rec-symbol-listp-of-rev))

(defmacro rec-u-hyps ()
  '(and (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (symbolp u)
        (r1cs::valuation-bindsp asg u)
        (equal (lookup-equal u asg) 1)))

(defruled rec-df-to-bits-when-bigp
  (implies (and bigp (not (equal bigp t)))
           (equal (values-dynamic-future-to-bits df bigp)
                  (values-dynamic-future-to-bits df t)))
  :enable (values-dynamic-future-to-bits values-field-to-bits))

(defruled rec-dfbits-sound
  (implies (and (rec-u-hyps)
                (rec-dfwp dfw)
                (rec-dftyped dfw asg)
                (r1cs::r1cs-constraints-holdp (rec-dfbits-gadget dfw u) asg p))
           (equal (ptx-terms-val (rec-dfbits-out dfw bigp) asg)
                  (values-dynamic-future-to-bits (rec-dfval dfw asg) bigp)))
  :do-not-induct t
  :cases ((equal bigp t))
  :use ((:instance rec-dynamic-future-write-bits-sound
                   (pn (nth 0 dfw)) (pw (nth 1 dfw)) (fn (nth 2 dfw))
                   (ck (nth 3 dfw)) (bitss (nth 4 dfw)) (rss (nth 5 dfw)))
        (:instance rec-symbol-listp-of-concat
                   (xs (rec-dfw-xs dfw)) (bitss (nth 4 dfw)) (rss (nth 5 dfw)))
        (:instance rec-terms-val-of-symbols
                   (xs (rec-concat-le (rec-dfw-xs dfw) (nth 4 dfw))))
        (:instance rec-terms-val-of-symbols
                   (xs (rec-concat-be (rec-dfw-xs dfw) (nth 4 dfw)))))
  :enable (rec-dfbits-out rec-dfbits-gadget rec-dfwp rec-dftyped rec-dfval
           rec-dfw-xs rec-bits-boundp rec-df-to-bits-when-bigp
           dynamic-future-to-bits-le dynamic-future-to-bits-be))

(defruled rec-dfbits-complete
  (implies (and (rec-u-hyps)
                (rec-dfwp dfw)
                (rec-dftyped dfw asg)
                (rec-bits-witness-okp asg (rec-dfw-xs dfw) (nth 4 dfw) (nth 5 dfw)))
           (r1cs::r1cs-constraints-holdp (rec-dfbits-gadget dfw u) asg p))
  :do-not-induct t
  :use ((:instance rec-dynamic-future-write-bits-complete
                   (pn (nth 0 dfw)) (pw (nth 1 dfw)) (fn (nth 2 dfw))
                   (ck (nth 3 dfw)) (bitss (nth 4 dfw)) (rss (nth 5 dfw))))
  :enable (rec-dfbits-gadget rec-dfwp rec-dftyped rec-dfw-xs rec-bits-boundp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The bit terms and the constraints.

(define rec-arg-len-bits (n bigp)
  :short "The constant U16 (or U32 above 65535) length prefix of an argument."
  (if (<= n 65535)
      (values-uint-to-bits n 16 bigp)
    (values-uint-to-bits n 32 bigp)))

(defines rec-fbits-out
  :flag-local nil
  (define rec-fbits-out (fw bigp)
    :measure (acl2-count fw)
    (if (consp fw)
        (b* ((pid-bits (if bigp
                           (program-id-to-bits-be (car fw))
                         (program-id-to-bits-le (car fw))))
             (fname-bits (values-identifier-to-bits (cadr fw) bigp)))
          (append (values-uint-to-bits (len pid-bits) 16 bigp)
                  pid-bits
                  (values-uint-to-bits (len fname-bits) 16 bigp)
                  fname-bits
                  (values-uint-to-bits (len (cddr fw)) 8 bigp)
                  (rec-asbits-out (cddr fw) bigp)))
      nil))
  (define rec-abits-out (aw bigp)
    :measure (acl2-count aw)
    (case (car aw)
      (:plaintext (cons 0 (ptx-bits-out (cdr aw) bigp)))
      (:future (cons 1 (rec-fbits-out (cdr aw) bigp)))
      (otherwise (cons 1 (append (repeat 12 0) (rec-dfbits-out (cdr aw) bigp))))))
  (define rec-asbits-out (aws bigp)
    :measure (acl2-count aws)
    (if (atom aws)
        nil
      (append (rec-arg-len-bits (len (rec-abits-out (car aws) bigp)) bigp)
              (rec-abits-out (car aws) bigp)
              (rec-asbits-out (cdr aws) bigp)))))

(defines rec-fbits-gadget
  (define rec-fbits-gadget (fw bigp u)
    :measure (acl2-count fw)
    (and (consp fw) (rec-asbits-gadget (cddr fw) bigp u)))
  (define rec-abits-gadget (aw bigp u)
    :measure (acl2-count aw)
    (case (car aw)
      (:plaintext (ptx-bits-gadget (cdr aw) bigp))
      (:future (rec-fbits-gadget (cdr aw) bigp u))
      (otherwise (rec-dfbits-gadget (cdr aw) u))))
  (define rec-asbits-gadget (aws bigp u)
    :measure (acl2-count aws)
    (if (atom aws)
        nil
      (append (rec-abits-gadget (car aws) bigp u)
              (rec-asbits-gadget (cdr aws) bigp u)))))

(defines rec-fbits-witnessp
  :short "snarkVM's witnesses: each plaintext argument's leaf witnesses
          (ptx-bits-witnessp) and each DynamicFuture argument's canonical bits
          and range-check witnesses (rec-bits-witness-okp)."
  (define rec-fbits-witnessp (fw bigp asg p)
    :measure (acl2-count fw)
    (and (consp fw) (rec-asbits-witnessp (cddr fw) bigp asg p)))
  (define rec-abits-witnessp (aw bigp asg p)
    :measure (acl2-count aw)
    (case (car aw)
      (:plaintext (ptx-bits-witnessp (cdr aw) bigp asg p))
      (:future (rec-fbits-witnessp (cdr aw) bigp asg p))
      (otherwise (rec-bits-witness-okp asg (rec-dfw-xs (cdr aw))
                                       (nth 4 (cdr aw)) (nth 5 (cdr aw))))))
  (define rec-asbits-witnessp (aws bigp asg p)
    :measure (acl2-count aws)
    (if (atom aws)
        t
      (and (rec-abits-witnessp (car aws) bigp asg p)
           (rec-asbits-witnessp (cdr aws) bigp asg p)))))

(defrule rec-bits-fns-of-atom
  (implies (atom aws)
           (and (equal (rec-asbits-out aws bigp) nil)
                (equal (rec-asbits-gadget aws bigp u) nil)
                (equal (rec-asbits-witnessp aws bigp asg p) t)))
  :enable (rec-asbits-out rec-asbits-gadget rec-asbits-witnessp))

(defruled rec-ptx-bits-out-sound-rw
  (implies (and (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt bigp) asg p)
                (primep p)
                (ptx-typed wt asg))
           (equal (ptx-terms-val (ptx-bits-out wt bigp) asg)
                  (values-plaintext-to-bits (ptx-val wt asg) bigp))))

(defruled rec-dfbits-sound-rw
  (implies (and (r1cs::r1cs-constraints-holdp (rec-dfbits-gadget dfw u) asg p)
                (rec-u-hyps)
                (rec-dfwp dfw)
                (rec-dftyped dfw asg))
           (equal (ptx-terms-val (rec-dfbits-out dfw bigp) asg)
                  (values-dynamic-future-to-bits (rec-dfval dfw asg) bigp)))
  :use rec-dfbits-sound)

(defruled rec-len-of-terms-val-rw
  (equal (len (ptx-terms-val xs asg)) (len xs)))

(defthm-rec-fbits-out-flag
  (defthm rec-fbits-sound
    (implies (and (rec-u-hyps)
                  (rec-fwp fw)
                  (rec-ftyped fw asg)
                  (r1cs::r1cs-constraints-holdp (rec-fbits-gadget fw bigp u)
                                                asg p))
             (equal (ptx-terms-val (rec-fbits-out fw bigp) asg)
                    (values-future-to-bits (rec-fval fw asg) bigp)))
    :flag rec-fbits-out)
  (defthm rec-abits-sound
    (implies (and (rec-u-hyps)
                  (rec-awp aw)
                  (rec-atyped aw asg)
                  (r1cs::r1cs-constraints-holdp (rec-abits-gadget aw bigp u)
                                                asg p))
             (equal (ptx-terms-val (rec-abits-out aw bigp) asg)
                    (values-argument-to-bits (rec-aval aw asg) bigp)))
    :flag rec-abits-out)
  (defthm rec-asbits-sound
    (implies (and (rec-u-hyps)
                  (rec-awsp aws)
                  (rec-atyped-list aws asg)
                  (r1cs::r1cs-constraints-holdp (rec-asbits-gadget aws bigp u)
                                                asg p))
             (equal (ptx-terms-val (rec-asbits-out aws bigp) asg)
                    (values-arguments-to-bits (rec-avals aws asg) bigp)))
    :flag rec-asbits-out)
  :hints (("Goal"
           :in-theory (enable values-future-to-bits values-argument-to-bits
                              values-arguments-to-bits rec-arg-len-bits
                              rec-ptx-bits-out-sound-rw rec-dfbits-sound-rw
                              r1cs::r1cs-constraints-holdp-of-append
                              primep-of-base-prime)
           :expand ((rec-fwp fw) (rec-awp aw) (rec-awsp aws)
                    (rec-fval fw asg) (rec-aval aw asg) (rec-avals aws asg)
                    (rec-ftyped fw asg) (rec-atyped aw asg)
                    (rec-atyped-list aws asg)
                    (rec-fbits-out fw bigp) (rec-abits-out aw bigp)
                    (rec-asbits-out aws bigp)
                    (rec-fbits-gadget fw bigp u) (rec-abits-gadget aw bigp u)
                    (rec-asbits-gadget aws bigp u)))))

(defthm-rec-fbits-out-flag
  (defthm rec-fbits-complete
    (implies (and (rec-u-hyps)
                  (rec-fwp fw)
                  (rec-ftyped fw asg)
                  (rec-fbits-witnessp fw bigp asg p))
             (r1cs::r1cs-constraints-holdp (rec-fbits-gadget fw bigp u) asg p))
    :flag rec-fbits-out)
  (defthm rec-abits-complete
    (implies (and (rec-u-hyps)
                  (rec-awp aw)
                  (rec-atyped aw asg)
                  (rec-abits-witnessp aw bigp asg p))
             (r1cs::r1cs-constraints-holdp (rec-abits-gadget aw bigp u) asg p))
    :flag rec-abits-out)
  (defthm rec-asbits-complete
    (implies (and (rec-u-hyps)
                  (rec-awsp aws)
                  (rec-atyped-list aws asg)
                  (rec-asbits-witnessp aws bigp asg p))
             (r1cs::r1cs-constraints-holdp (rec-asbits-gadget aws bigp u) asg p))
    :flag rec-asbits-out)
  :hints (("Goal"
           :in-theory (enable ptx-bits-gadget-complete rec-dfbits-complete
                              r1cs::r1cs-constraints-holdp-of-append
                              primep-of-base-prime)
           :expand ((rec-fwp fw) (rec-awp aw) (rec-awsp aws)
                    (rec-ftyped fw asg) (rec-atyped aw asg)
                    (rec-atyped-list aws asg)
                    (:free (p) (rec-fbits-witnessp fw bigp asg p))
                    (:free (p) (rec-abits-witnessp aw bigp asg p))
                    (:free (p) (rec-asbits-witnessp aws bigp asg p))
                    (rec-fbits-gadget fw bigp u) (rec-abits-gadget aw bigp u)
                    (rec-asbits-gadget aws bigp u)))))

(in-theory (disable rec-fbits-sound rec-abits-sound rec-asbits-sound
                    rec-fbits-complete rec-abits-complete rec-asbits-complete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; The row theorems.

(defmacro rec-fbits-hyps ()
  '(and (rec-u-hyps) (rec-fwp fw) (rec-ftyped fw asg)))

(defruled rec-future-write-bits-le-sound
  (implies (and (rec-fbits-hyps)
                (r1cs::r1cs-constraints-holdp (rec-fbits-gadget fw nil u) asg p))
           (equal (ptx-terms-val (rec-fbits-out fw nil) asg)
                  (future-to-bits-le (rec-fval fw asg))))
  :use (:instance rec-fbits-sound (bigp nil))
  :enable future-to-bits-le)

(defruled rec-future-write-bits-be-sound
  (implies (and (rec-fbits-hyps)
                (r1cs::r1cs-constraints-holdp (rec-fbits-gadget fw t u) asg p))
           (equal (ptx-terms-val (rec-fbits-out fw t) asg)
                  (future-to-bits-be (rec-fval fw asg))))
  :use (:instance rec-fbits-sound (bigp t))
  :enable future-to-bits-be)

(defruled rec-future-write-bits-complete
  (implies (and (rec-fbits-hyps)
                (rec-fbits-witnessp fw bigp asg p))
           (r1cs::r1cs-constraints-holdp (rec-fbits-gadget fw bigp u) asg p))
  :use rec-fbits-complete)

(defmacro rec-abits-hyps ()
  '(and (rec-u-hyps) (rec-awp aw) (rec-atyped aw asg)))

(defruled rec-argument-write-bits-le-sound
  (implies (and (rec-abits-hyps)
                (r1cs::r1cs-constraints-holdp (rec-abits-gadget aw nil u) asg p))
           (equal (ptx-terms-val (rec-abits-out aw nil) asg)
                  (argument-to-bits-le (rec-aval aw asg))))
  :use (:instance rec-abits-sound (bigp nil))
  :enable argument-to-bits-le)

(defruled rec-argument-write-bits-be-sound
  (implies (and (rec-abits-hyps)
                (r1cs::r1cs-constraints-holdp (rec-abits-gadget aw t u) asg p))
           (equal (ptx-terms-val (rec-abits-out aw t) asg)
                  (argument-to-bits-be (rec-aval aw asg))))
  :use (:instance rec-abits-sound (bigp t))
  :enable argument-to-bits-be)

(defruled rec-argument-write-bits-complete
  (implies (and (rec-abits-hyps)
                (rec-abits-witnessp aw bigp asg p))
           (r1cs::r1cs-constraints-holdp (rec-abits-gadget aw bigp u) asg p))
  :use rec-abits-complete)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; to_fields: write_bits_le, a constant 1, packed into fields (linear, no
; constraints of its own); snarkVM halts when the bits need more fields than
; the maximum, as values-pack-bits-bounded returns an error.

(define rec-future-to-fields-out (fw)
  (ptx-to-fields-out (append (rec-fbits-out fw nil) (list 1))))

(defruled rec-future-to-fields-sound
  (b* ((out (rec-future-to-fields-out fw))
       (spec (future-to-fields (rec-fval fw asg))))
    (implies (and (rec-fbits-hyps)
                  (r1cs::r1cs-constraints-holdp (rec-fbits-gadget fw nil u) asg p))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-chunks-val out asg) spec)))))
  :do-not-induct t
  :use ((:instance rec-future-write-bits-le-sound)
        (:instance ptx-to-fields-out-correct
                   (terms (append (rec-fbits-out fw nil) (list 1)))))
  :enable (rec-future-to-fields-out future-to-fields))
