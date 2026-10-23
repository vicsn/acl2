; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; DynamicFuture (snarkVM circuit/program/src/data/dynamic/future):
; four field elements program_name, program_network, function_name, checksum
; (the console arguments are not circuit values).
;
; new:            Field::new on each: witnesses, no constraint.
; write_bits_*:   Field::write_bits_* on the four fields in order: the vector
;                 gadget rec-fields-write-bits-gadget on (pn pw fn ck).
; to_fields:      to_bits_le, push the constant true, chunk by 252 bits,
;                 Field::from_bits_le per chunk.  A chunk of at most 252 bits
;                 adds no constraint; the field is the linear combination
;                 sum 2^i b_i, whose value is values-lebits-to-field of the
;                 chunk.  So the constraints are exactly write_bits_le's.

(in-package "ALEOVM")

(include-book "rec-ciphertext")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rec-dynamic-future-of-wires ((pn symbolp) (pw symbolp)
                                     (fn symbolp) (ck symbolp)
                                     (asg alistp))
  :verify-guards nil
  :returns (df dynamic-futurep)
  (dynamic-future (lookup-equal pn asg) (lookup-equal pw asg)
                  (lookup-equal fn asg) (lookup-equal ck asg)))

(defmacro rec-df-wire-hyps ()
  '(and (symbolp pn) (symbolp pw) (symbolp fn) (symbolp ck)
        (r1cs::r1cs-valuationp asg (base-prime))
        (r1cs::valuation-bindsp asg pn)
        (r1cs::valuation-bindsp asg pw)
        (r1cs::valuation-bindsp asg fn)
        (r1cs::valuation-bindsp asg ck)))

(defruled rec-df-fields
  (implies (rec-df-wire-hyps)
           (b* ((df (rec-dynamic-future-of-wires pn pw fn ck asg)))
             (and (equal (dynamic-future->program-name df) (lookup-equal pn asg))
                  (equal (dynamic-future->program-network df) (lookup-equal pw asg))
                  (equal (dynamic-future->function-name df) (lookup-equal fn asg))
                  (equal (dynamic-future->checksum df) (lookup-equal ck asg)))))
  :enable (rec-dynamic-future-of-wires fieldp
           r1cs::fep-of-lookup-equal primep-of-base-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DynamicFuture::new

(define rec-dynamic-future-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Constraints of @('DynamicFuture::new') in variable mode: none."
  nil)

(defruled rec-dynamic-future-new-sound
  (implies (and (rec-df-wire-hyps)
                (r1cs::r1cs-constraints-holdp (rec-dynamic-future-new-gadget)
                                              asg (base-prime)))
           (b* ((df (rec-dynamic-future-of-wires pn pw fn ck asg)))
             (and (dynamic-futurep df)
                  (equal (dynamic-future-new df) df)
                  (equal (dynamic-future->program-name df) (lookup-equal pn asg))
                  (equal (dynamic-future->program-network df) (lookup-equal pw asg))
                  (equal (dynamic-future->function-name df) (lookup-equal fn asg))
                  (equal (dynamic-future->checksum df) (lookup-equal ck asg)))))
  :enable (dynamic-future-new rec-df-fields))

(defruled rec-dynamic-future-new-complete
  (r1cs::r1cs-constraints-holdp (rec-dynamic-future-new-gadget) asg p)
  :enable (rec-dynamic-future-new-gadget r1cs::r1cs-constraints-holdp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DynamicFuture::write_bits_le / write_bits_be

(define rec-dynamic-future-write-bits-gadget ((pn symbolp) (pw symbolp)
                                              (fn symbolp) (ck symbolp)
                                              bitss rss (u symbolp))
  :guard (rec-bits-shapep (list pn pw fn ck) bitss rss)
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp (and (symbolp pn) (symbolp pw) (symbolp fn) (symbolp ck)
                              (symbolp u)
                              (rec-bits-shapep (list pn pw fn ck) bitss rss)))
  :short "Constraints of @('DynamicFuture::write_bits_le') and
          @('write_bits_be'): Field::write_bits_le on each of the four fields."
  (rec-fields-write-bits-gadget (list pn pw fn ck) bitss rss u))

(defruled rec-df-bits-of-fields
  (implies (and (fieldp a) (fieldp b) (fieldp c) (fieldp d))
           (and (equal (crypto-field-list-bits-le (list a b c d))
                       (values-dynamic-future-to-bits (dynamic-future a b c d) nil))
                (equal (crypto-field-list-bits-be (list a b c d))
                       (values-dynamic-future-to-bits (dynamic-future a b c d) t))))
  :enable (crypto-field-list-bits-le crypto-field-list-bits-be
           values-dynamic-future-to-bits
           rec-crypto-field-bits rec-values-field-to-bits))

(defmacro rec-df-bits-hyps ()
  '(b* ((xs (list pn pw fn ck)))
     (and (rec-df-wire-hyps)
          (symbolp u)
          (rec-bits-shapep xs bitss rss)
          (r1cs::valuation-bindsp asg u)
          (equal (lookup-equal u asg) 1)
          (rec-bits-boundp asg xs bitss rss))))

(defruled rec-dynamic-future-write-bits-sound
  (b* ((xs (list pn pw fn ck))
       (df (rec-dynamic-future-of-wires pn pw fn ck asg)))
    (implies (and (rec-df-bits-hyps)
                  (r1cs::r1cs-constraints-holdp
                   (rec-dynamic-future-write-bits-gadget pn pw fn ck bitss rss u)
                   asg (base-prime)))
             (and (dynamic-futurep df)
                  (equal (lookup-equal-list (rec-concat-le xs bitss) asg)
                         (dynamic-future-to-bits-le df))
                  (equal (lookup-equal-list (rec-concat-be xs bitss) asg)
                         (dynamic-future-to-bits-be df)))))
  :do-not-induct t
  :enable (rec-dynamic-future-write-bits-gadget
           dynamic-future-to-bits-le dynamic-future-to-bits-be
           rec-dynamic-future-of-wires
           rec-df-bits-of-fields
           lookup-equal-list fieldp
           r1cs::fep-of-lookup-equal primep-of-base-prime)
  :use (:instance rec-fields-write-bits-sound (xs (list pn pw fn ck))))

(defruled rec-dynamic-future-write-bits-complete
  (b* ((xs (list pn pw fn ck)))
    (implies (and (rec-df-bits-hyps)
                  (rec-bits-witness-okp asg xs bitss rss))
             (r1cs::r1cs-constraints-holdp
              (rec-dynamic-future-write-bits-gadget pn pw fn ck bitss rss u)
              asg (base-prime))))
  :enable rec-dynamic-future-write-bits-gadget
  :use (:instance rec-fields-write-bits-complete (xs (list pn pw fn ck))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; DynamicFuture::to_fields

(defruled rec-len-of-values-pack-bits-bound
  (implies (and (natp k)
                (<= (len bits) (* 252 k)))
           (<= (len (values-pack-bits bits)) k))
  :induct (rec-pack-induct bits k)
  :enable values-pack-bits
  :prep-lemmas
  ((defun rec-pack-induct (bits k)
     (declare (xargs :measure (len bits)))
     (if (or (endp bits) (zp k))
         (list bits k)
       (rec-pack-induct (nthcdr 252 bits) (1- k))))))

(define rec-dynamic-future-to-fields-value ((bitvals bit-listp))
  :short "Values of the output fields: each 252-bit chunk of the bits and the
          trailing constant 1 is the linear combination @($\\sum 2^i b_i$)
          (Field::from_bits_le of at most 252 bits), reduced modulo p."
  (values-pack-bits (append bitvals (list 1))))

(defruled rec-len-of-dynamic-future-to-bits-le
  (equal (len (dynamic-future-to-bits-le df)) 1012)
  :enable (dynamic-future-to-bits-le values-dynamic-future-to-bits
           values-field-to-bits))

(defruled rec-dynamic-future-to-fields-unbounded
  (equal (dynamic-future-to-fields df)
         (values-pack-bits (append (dynamic-future-to-bits-le df) (list 1))))
  :do-not-induct t
  :enable (dynamic-future-to-fields values-pack-bits-bounded
           values-max-data-size-in-fields rec-len-of-dynamic-future-to-bits-le)
  :use (:instance rec-len-of-values-pack-bits-bound
                  (bits (append (dynamic-future-to-bits-le df) (list 1)))
                  (k 5)))

(defruled rec-dynamic-future-to-fields-sound
  (b* ((xs (list pn pw fn ck))
       (df (rec-dynamic-future-of-wires pn pw fn ck asg)))
    (implies (and (rec-df-bits-hyps)
                  (r1cs::r1cs-constraints-holdp
                   (rec-dynamic-future-write-bits-gadget pn pw fn ck bitss rss u)
                   asg (base-prime)))
             (equal (rec-dynamic-future-to-fields-value
                     (lookup-equal-list (rec-concat-le xs bitss) asg))
                    (dynamic-future-to-fields df))))
  :do-not-induct t
  :in-theory (e/d (rec-dynamic-future-to-fields-value
                   rec-dynamic-future-to-fields-unbounded)
                  (dynamic-future-to-bits-le dynamic-future-to-fields))
  :use rec-dynamic-future-write-bits-sound)
