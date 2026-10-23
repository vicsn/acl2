; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Environment functions that add no constraints of their own.
;
;   to_bits_* / write_bits_* concatenate element bits.  The element
;   write is the abstract write-bits-*-impl; this function only
;   sequences the calls.
;   Inject::new for Vec and tuples sequences inject-impl.
;   recursively_replace_self and rename_selfs are proc-macros on token
;   streams.  They are not circuits.
;
; The gadget is empty.  Soundness and completeness are the funspec
; equation (one expansion) together with the empty constraint list.
; The PFCS body is empty, so the lifted predicate is true exactly when
; the gadget holds.

(in-package "ALEOVM")

(include-book "../fun-specs/primitives-environment")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *val-env-empty-sample* nil)

(defruled val-env-empty-sample-holds
  (r1cs::r1cs-constraints-holdp nil *val-env-empty-sample* (base-prime))
  :enable r1cs::r1cs-constraints-holdp)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vec-write-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Vec::write_bits_le concatenates little-endian element bits."
  nil)

(defruled vec-write-bits-le-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (r1cs::r1cs-constraints-holdp (vec-write-bits-le-gadget) asg p))
           (equal (write-bits-le-seq-funspec acc elems)
                  (if (endp elems)
                      acc
                    (write-bits-le-seq-funspec (write-bits-le-impl acc (car elems))
                           (cdr elems)))))
  :hints (("Goal" :expand ((write-bits-le-seq-funspec acc elems)
                          (write-bits-le-seq-funspec acc nil))
                  :in-theory (enable vec-write-bits-le-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled vec-write-bits-le-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (equal (write-bits-le-seq-funspec acc elems)
                       (if (endp elems)
                      acc
                    (write-bits-le-seq-funspec (write-bits-le-impl acc (car elems))
                           (cdr elems)))))
           (r1cs::r1cs-constraints-holdp (vec-write-bits-le-gadget) asg p))
  :hints (("Goal" :expand ((write-bits-le-seq-funspec acc elems))
                  :in-theory (enable vec-write-bits-le-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *vec-write-bits-le-sample* *val-env-empty-sample*)

(defruled vec-write-bits-le-sample-holds
  (r1cs::r1cs-constraints-holdp (vec-write-bits-le-gadget)
                                *vec-write-bits-le-sample*
                                (base-prime))
  :enable (vec-write-bits-le-gadget val-env-empty-sample-holds)
  )

(define vec-write-bits-le-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "vec_write_bits_le() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (vec-write-bits-le-circuit)
            :pred vec-write-bits-le-pred
            :prime prime)

(defruled vec-write-bits-le-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (vec-write-bits-le-pred prime)
                  (r1cs::r1cs-constraints-holdp (vec-write-bits-le-gadget) nil prime)))
  :enable (vec-write-bits-le-pred vec-write-bits-le-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vec-write-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Vec::write_bits_be concatenates big-endian element bits."
  nil)

(defruled vec-write-bits-be-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (r1cs::r1cs-constraints-holdp (vec-write-bits-be-gadget) asg p))
           (equal (write-bits-be-seq-funspec acc elems)
                  (if (endp elems)
                      acc
                    (write-bits-be-seq-funspec (write-bits-be-impl acc (car elems))
                           (cdr elems)))))
  :hints (("Goal" :expand ((write-bits-be-seq-funspec acc elems)
                          (write-bits-be-seq-funspec acc nil))
                  :in-theory (enable vec-write-bits-be-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled vec-write-bits-be-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (equal (write-bits-be-seq-funspec acc elems)
                       (if (endp elems)
                      acc
                    (write-bits-be-seq-funspec (write-bits-be-impl acc (car elems))
                           (cdr elems)))))
           (r1cs::r1cs-constraints-holdp (vec-write-bits-be-gadget) asg p))
  :hints (("Goal" :expand ((write-bits-be-seq-funspec acc elems))
                  :in-theory (enable vec-write-bits-be-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *vec-write-bits-be-sample* *val-env-empty-sample*)

(defruled vec-write-bits-be-sample-holds
  (r1cs::r1cs-constraints-holdp (vec-write-bits-be-gadget)
                                *vec-write-bits-be-sample*
                                (base-prime))
  :enable (vec-write-bits-be-gadget val-env-empty-sample-holds)
  )

(define vec-write-bits-be-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "vec_write_bits_be() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (vec-write-bits-be-circuit)
            :pred vec-write-bits-be-pred
            :prime prime)

(defruled vec-write-bits-be-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (vec-write-bits-be-pred prime)
                  (r1cs::r1cs-constraints-holdp (vec-write-bits-be-gadget) nil prime)))
  :enable (vec-write-bits-be-pred vec-write-bits-be-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vec-write-bits-raw-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Vec::write_bits_raw_le concatenates raw little-endian element bits."
  nil)

(defruled vec-write-bits-raw-le-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (r1cs::r1cs-constraints-holdp (vec-write-bits-raw-le-gadget) asg p))
           (equal (write-bits-raw-le-seq-funspec acc elems)
                  (if (endp elems)
                      acc
                    (write-bits-raw-le-seq-funspec (write-bits-raw-le-impl acc (car elems))
                           (cdr elems)))))
  :hints (("Goal" :expand ((write-bits-raw-le-seq-funspec acc elems)
                          (write-bits-raw-le-seq-funspec acc nil))
                  :in-theory (enable vec-write-bits-raw-le-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled vec-write-bits-raw-le-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (equal (write-bits-raw-le-seq-funspec acc elems)
                       (if (endp elems)
                      acc
                    (write-bits-raw-le-seq-funspec (write-bits-raw-le-impl acc (car elems))
                           (cdr elems)))))
           (r1cs::r1cs-constraints-holdp (vec-write-bits-raw-le-gadget) asg p))
  :hints (("Goal" :expand ((write-bits-raw-le-seq-funspec acc elems))
                  :in-theory (enable vec-write-bits-raw-le-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *vec-write-bits-raw-le-sample* *val-env-empty-sample*)

(defruled vec-write-bits-raw-le-sample-holds
  (r1cs::r1cs-constraints-holdp (vec-write-bits-raw-le-gadget)
                                *vec-write-bits-raw-le-sample*
                                (base-prime))
  :enable (vec-write-bits-raw-le-gadget val-env-empty-sample-holds)
  )

(define vec-write-bits-raw-le-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "vec_write_bits_raw_le() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (vec-write-bits-raw-le-circuit)
            :pred vec-write-bits-raw-le-pred
            :prime prime)

(defruled vec-write-bits-raw-le-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (vec-write-bits-raw-le-pred prime)
                  (r1cs::r1cs-constraints-holdp (vec-write-bits-raw-le-gadget) nil prime)))
  :enable (vec-write-bits-raw-le-pred vec-write-bits-raw-le-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vec-write-bits-raw-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Vec::write_bits_raw_be concatenates raw big-endian element bits."
  nil)

(defruled vec-write-bits-raw-be-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (r1cs::r1cs-constraints-holdp (vec-write-bits-raw-be-gadget) asg p))
           (equal (write-bits-raw-be-seq-funspec acc elems)
                  (if (endp elems)
                      acc
                    (write-bits-raw-be-seq-funspec (write-bits-raw-be-impl acc (car elems))
                           (cdr elems)))))
  :hints (("Goal" :expand ((write-bits-raw-be-seq-funspec acc elems)
                          (write-bits-raw-be-seq-funspec acc nil))
                  :in-theory (enable vec-write-bits-raw-be-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled vec-write-bits-raw-be-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (equal (write-bits-raw-be-seq-funspec acc elems)
                       (if (endp elems)
                      acc
                    (write-bits-raw-be-seq-funspec (write-bits-raw-be-impl acc (car elems))
                           (cdr elems)))))
           (r1cs::r1cs-constraints-holdp (vec-write-bits-raw-be-gadget) asg p))
  :hints (("Goal" :expand ((write-bits-raw-be-seq-funspec acc elems))
                  :in-theory (enable vec-write-bits-raw-be-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *vec-write-bits-raw-be-sample* *val-env-empty-sample*)

(defruled vec-write-bits-raw-be-sample-holds
  (r1cs::r1cs-constraints-holdp (vec-write-bits-raw-be-gadget)
                                *vec-write-bits-raw-be-sample*
                                (base-prime))
  :enable (vec-write-bits-raw-be-gadget val-env-empty-sample-holds)
  )

(define vec-write-bits-raw-be-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "vec_write_bits_raw_be() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (vec-write-bits-raw-be-circuit)
            :pred vec-write-bits-raw-be-pred
            :prime prime)

(defruled vec-write-bits-raw-be-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (vec-write-bits-raw-be-pred prime)
                  (r1cs::r1cs-constraints-holdp (vec-write-bits-raw-be-gadget) nil prime)))
  :enable (vec-write-bits-raw-be-pred vec-write-bits-raw-be-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define array-write-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "[C]::write_bits_le concatenates little-endian element bits."
  nil)

(defruled array-write-bits-le-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (r1cs::r1cs-constraints-holdp (array-write-bits-le-gadget) asg p))
           (equal (write-bits-le-seq-funspec acc elems)
                  (if (endp elems)
                      acc
                    (write-bits-le-seq-funspec (write-bits-le-impl acc (car elems))
                           (cdr elems)))))
  :hints (("Goal" :expand ((write-bits-le-seq-funspec acc elems)
                          (write-bits-le-seq-funspec acc nil))
                  :in-theory (enable array-write-bits-le-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled array-write-bits-le-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (equal (write-bits-le-seq-funspec acc elems)
                       (if (endp elems)
                      acc
                    (write-bits-le-seq-funspec (write-bits-le-impl acc (car elems))
                           (cdr elems)))))
           (r1cs::r1cs-constraints-holdp (array-write-bits-le-gadget) asg p))
  :hints (("Goal" :expand ((write-bits-le-seq-funspec acc elems))
                  :in-theory (enable array-write-bits-le-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *array-write-bits-le-sample* *val-env-empty-sample*)

(defruled array-write-bits-le-sample-holds
  (r1cs::r1cs-constraints-holdp (array-write-bits-le-gadget)
                                *array-write-bits-le-sample*
                                (base-prime))
  :enable (array-write-bits-le-gadget val-env-empty-sample-holds)
  )

(define array-write-bits-le-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "array_write_bits_le() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (array-write-bits-le-circuit)
            :pred array-write-bits-le-pred
            :prime prime)

(defruled array-write-bits-le-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (array-write-bits-le-pred prime)
                  (r1cs::r1cs-constraints-holdp (array-write-bits-le-gadget) nil prime)))
  :enable (array-write-bits-le-pred array-write-bits-le-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define array-write-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "[C]::write_bits_be concatenates big-endian element bits."
  nil)

(defruled array-write-bits-be-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (r1cs::r1cs-constraints-holdp (array-write-bits-be-gadget) asg p))
           (equal (write-bits-be-seq-funspec acc elems)
                  (if (endp elems)
                      acc
                    (write-bits-be-seq-funspec (write-bits-be-impl acc (car elems))
                           (cdr elems)))))
  :hints (("Goal" :expand ((write-bits-be-seq-funspec acc elems)
                          (write-bits-be-seq-funspec acc nil))
                  :in-theory (enable array-write-bits-be-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled array-write-bits-be-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (equal (write-bits-be-seq-funspec acc elems)
                       (if (endp elems)
                      acc
                    (write-bits-be-seq-funspec (write-bits-be-impl acc (car elems))
                           (cdr elems)))))
           (r1cs::r1cs-constraints-holdp (array-write-bits-be-gadget) asg p))
  :hints (("Goal" :expand ((write-bits-be-seq-funspec acc elems))
                  :in-theory (enable array-write-bits-be-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *array-write-bits-be-sample* *val-env-empty-sample*)

(defruled array-write-bits-be-sample-holds
  (r1cs::r1cs-constraints-holdp (array-write-bits-be-gadget)
                                *array-write-bits-be-sample*
                                (base-prime))
  :enable (array-write-bits-be-gadget val-env-empty-sample-holds)
  )

(define array-write-bits-be-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "array_write_bits_be() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (array-write-bits-be-circuit)
            :pred array-write-bits-be-pred
            :prime prime)

(defruled array-write-bits-be-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (array-write-bits-be-pred prime)
                  (r1cs::r1cs-constraints-holdp (array-write-bits-be-gadget) nil prime)))
  :enable (array-write-bits-be-pred array-write-bits-be-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define array-write-bits-raw-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "[C]::write_bits_raw_le concatenates raw little-endian element bits."
  nil)

(defruled array-write-bits-raw-le-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (r1cs::r1cs-constraints-holdp (array-write-bits-raw-le-gadget) asg p))
           (equal (write-bits-raw-le-seq-funspec acc elems)
                  (if (endp elems)
                      acc
                    (write-bits-raw-le-seq-funspec (write-bits-raw-le-impl acc (car elems))
                           (cdr elems)))))
  :hints (("Goal" :expand ((write-bits-raw-le-seq-funspec acc elems)
                          (write-bits-raw-le-seq-funspec acc nil))
                  :in-theory (enable array-write-bits-raw-le-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled array-write-bits-raw-le-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (equal (write-bits-raw-le-seq-funspec acc elems)
                       (if (endp elems)
                      acc
                    (write-bits-raw-le-seq-funspec (write-bits-raw-le-impl acc (car elems))
                           (cdr elems)))))
           (r1cs::r1cs-constraints-holdp (array-write-bits-raw-le-gadget) asg p))
  :hints (("Goal" :expand ((write-bits-raw-le-seq-funspec acc elems))
                  :in-theory (enable array-write-bits-raw-le-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *array-write-bits-raw-le-sample* *val-env-empty-sample*)

(defruled array-write-bits-raw-le-sample-holds
  (r1cs::r1cs-constraints-holdp (array-write-bits-raw-le-gadget)
                                *array-write-bits-raw-le-sample*
                                (base-prime))
  :enable (array-write-bits-raw-le-gadget val-env-empty-sample-holds)
  )

(define array-write-bits-raw-le-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "array_write_bits_raw_le() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (array-write-bits-raw-le-circuit)
            :pred array-write-bits-raw-le-pred
            :prime prime)

(defruled array-write-bits-raw-le-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (array-write-bits-raw-le-pred prime)
                  (r1cs::r1cs-constraints-holdp (array-write-bits-raw-le-gadget) nil prime)))
  :enable (array-write-bits-raw-le-pred array-write-bits-raw-le-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define array-write-bits-raw-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "[C]::write_bits_raw_be concatenates raw big-endian element bits."
  nil)

(defruled array-write-bits-raw-be-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (r1cs::r1cs-constraints-holdp (array-write-bits-raw-be-gadget) asg p))
           (equal (write-bits-raw-be-seq-funspec acc elems)
                  (if (endp elems)
                      acc
                    (write-bits-raw-be-seq-funspec (write-bits-raw-be-impl acc (car elems))
                           (cdr elems)))))
  :hints (("Goal" :expand ((write-bits-raw-be-seq-funspec acc elems)
                          (write-bits-raw-be-seq-funspec acc nil))
                  :in-theory (enable array-write-bits-raw-be-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled array-write-bits-raw-be-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (equal (write-bits-raw-be-seq-funspec acc elems)
                       (if (endp elems)
                      acc
                    (write-bits-raw-be-seq-funspec (write-bits-raw-be-impl acc (car elems))
                           (cdr elems)))))
           (r1cs::r1cs-constraints-holdp (array-write-bits-raw-be-gadget) asg p))
  :hints (("Goal" :expand ((write-bits-raw-be-seq-funspec acc elems))
                  :in-theory (enable array-write-bits-raw-be-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *array-write-bits-raw-be-sample* *val-env-empty-sample*)

(defruled array-write-bits-raw-be-sample-holds
  (r1cs::r1cs-constraints-holdp (array-write-bits-raw-be-gadget)
                                *array-write-bits-raw-be-sample*
                                (base-prime))
  :enable (array-write-bits-raw-be-gadget val-env-empty-sample-holds)
  )

(define array-write-bits-raw-be-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "array_write_bits_raw_be() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (array-write-bits-raw-be-circuit)
            :pred array-write-bits-raw-be-pred
            :prime prime)

(defruled array-write-bits-raw-be-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (array-write-bits-raw-be-pred prime)
                  (r1cs::r1cs-constraints-holdp (array-write-bits-raw-be-gadget) nil prime)))
  :enable (array-write-bits-raw-be-pred array-write-bits-raw-be-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tuple-write-bits-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Tuple write_bits_le concatenates little-endian component bits."
  nil)

(defruled tuple-write-bits-le-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (r1cs::r1cs-constraints-holdp (tuple-write-bits-le-gadget) asg p))
           (equal (write-bits-le-seq-funspec acc elems)
                  (if (endp elems)
                      acc
                    (write-bits-le-seq-funspec (write-bits-le-impl acc (car elems))
                           (cdr elems)))))
  :hints (("Goal" :expand ((write-bits-le-seq-funspec acc elems)
                          (write-bits-le-seq-funspec acc nil))
                  :in-theory (enable tuple-write-bits-le-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled tuple-write-bits-le-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (equal (write-bits-le-seq-funspec acc elems)
                       (if (endp elems)
                      acc
                    (write-bits-le-seq-funspec (write-bits-le-impl acc (car elems))
                           (cdr elems)))))
           (r1cs::r1cs-constraints-holdp (tuple-write-bits-le-gadget) asg p))
  :hints (("Goal" :expand ((write-bits-le-seq-funspec acc elems))
                  :in-theory (enable tuple-write-bits-le-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *tuple-write-bits-le-sample* *val-env-empty-sample*)

(defruled tuple-write-bits-le-sample-holds
  (r1cs::r1cs-constraints-holdp (tuple-write-bits-le-gadget)
                                *tuple-write-bits-le-sample*
                                (base-prime))
  :enable (tuple-write-bits-le-gadget val-env-empty-sample-holds)
  )

(define tuple-write-bits-le-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "tuple_write_bits_le() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (tuple-write-bits-le-circuit)
            :pred tuple-write-bits-le-pred
            :prime prime)

(defruled tuple-write-bits-le-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (tuple-write-bits-le-pred prime)
                  (r1cs::r1cs-constraints-holdp (tuple-write-bits-le-gadget) nil prime)))
  :enable (tuple-write-bits-le-pred tuple-write-bits-le-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tuple-write-bits-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Tuple write_bits_be concatenates big-endian component bits."
  nil)

(defruled tuple-write-bits-be-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (r1cs::r1cs-constraints-holdp (tuple-write-bits-be-gadget) asg p))
           (equal (write-bits-be-seq-funspec acc elems)
                  (if (endp elems)
                      acc
                    (write-bits-be-seq-funspec (write-bits-be-impl acc (car elems))
                           (cdr elems)))))
  :hints (("Goal" :expand ((write-bits-be-seq-funspec acc elems)
                          (write-bits-be-seq-funspec acc nil))
                  :in-theory (enable tuple-write-bits-be-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled tuple-write-bits-be-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (equal (write-bits-be-seq-funspec acc elems)
                       (if (endp elems)
                      acc
                    (write-bits-be-seq-funspec (write-bits-be-impl acc (car elems))
                           (cdr elems)))))
           (r1cs::r1cs-constraints-holdp (tuple-write-bits-be-gadget) asg p))
  :hints (("Goal" :expand ((write-bits-be-seq-funspec acc elems))
                  :in-theory (enable tuple-write-bits-be-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *tuple-write-bits-be-sample* *val-env-empty-sample*)

(defruled tuple-write-bits-be-sample-holds
  (r1cs::r1cs-constraints-holdp (tuple-write-bits-be-gadget)
                                *tuple-write-bits-be-sample*
                                (base-prime))
  :enable (tuple-write-bits-be-gadget val-env-empty-sample-holds)
  )

(define tuple-write-bits-be-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "tuple_write_bits_be() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (tuple-write-bits-be-circuit)
            :pred tuple-write-bits-be-pred
            :prime prime)

(defruled tuple-write-bits-be-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (tuple-write-bits-be-pred prime)
                  (r1cs::r1cs-constraints-holdp (tuple-write-bits-be-gadget) nil prime)))
  :enable (tuple-write-bits-be-pred tuple-write-bits-be-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tuple-write-bits-raw-le-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Tuple write_bits_raw_le concatenates raw little-endian component bits."
  nil)

(defruled tuple-write-bits-raw-le-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (r1cs::r1cs-constraints-holdp (tuple-write-bits-raw-le-gadget) asg p))
           (equal (write-bits-raw-le-seq-funspec acc elems)
                  (if (endp elems)
                      acc
                    (write-bits-raw-le-seq-funspec (write-bits-raw-le-impl acc (car elems))
                           (cdr elems)))))
  :hints (("Goal" :expand ((write-bits-raw-le-seq-funspec acc elems)
                          (write-bits-raw-le-seq-funspec acc nil))
                  :in-theory (enable tuple-write-bits-raw-le-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled tuple-write-bits-raw-le-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (equal (write-bits-raw-le-seq-funspec acc elems)
                       (if (endp elems)
                      acc
                    (write-bits-raw-le-seq-funspec (write-bits-raw-le-impl acc (car elems))
                           (cdr elems)))))
           (r1cs::r1cs-constraints-holdp (tuple-write-bits-raw-le-gadget) asg p))
  :hints (("Goal" :expand ((write-bits-raw-le-seq-funspec acc elems))
                  :in-theory (enable tuple-write-bits-raw-le-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *tuple-write-bits-raw-le-sample* *val-env-empty-sample*)

(defruled tuple-write-bits-raw-le-sample-holds
  (r1cs::r1cs-constraints-holdp (tuple-write-bits-raw-le-gadget)
                                *tuple-write-bits-raw-le-sample*
                                (base-prime))
  :enable (tuple-write-bits-raw-le-gadget val-env-empty-sample-holds)
  )

(define tuple-write-bits-raw-le-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "tuple_write_bits_raw_le() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (tuple-write-bits-raw-le-circuit)
            :pred tuple-write-bits-raw-le-pred
            :prime prime)

(defruled tuple-write-bits-raw-le-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (tuple-write-bits-raw-le-pred prime)
                  (r1cs::r1cs-constraints-holdp (tuple-write-bits-raw-le-gadget) nil prime)))
  :enable (tuple-write-bits-raw-le-pred tuple-write-bits-raw-le-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tuple-write-bits-raw-be-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Tuple write_bits_raw_be concatenates raw big-endian component bits."
  nil)

(defruled tuple-write-bits-raw-be-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (r1cs::r1cs-constraints-holdp (tuple-write-bits-raw-be-gadget) asg p))
           (equal (write-bits-raw-be-seq-funspec acc elems)
                  (if (endp elems)
                      acc
                    (write-bits-raw-be-seq-funspec (write-bits-raw-be-impl acc (car elems))
                           (cdr elems)))))
  :hints (("Goal" :expand ((write-bits-raw-be-seq-funspec acc elems)
                          (write-bits-raw-be-seq-funspec acc nil))
                  :in-theory (enable tuple-write-bits-raw-be-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled tuple-write-bits-raw-be-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp elems)
                (equal (write-bits-raw-be-seq-funspec acc elems)
                       (if (endp elems)
                      acc
                    (write-bits-raw-be-seq-funspec (write-bits-raw-be-impl acc (car elems))
                           (cdr elems)))))
           (r1cs::r1cs-constraints-holdp (tuple-write-bits-raw-be-gadget) asg p))
  :hints (("Goal" :expand ((write-bits-raw-be-seq-funspec acc elems))
                  :in-theory (enable tuple-write-bits-raw-be-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *tuple-write-bits-raw-be-sample* *val-env-empty-sample*)

(defruled tuple-write-bits-raw-be-sample-holds
  (r1cs::r1cs-constraints-holdp (tuple-write-bits-raw-be-gadget)
                                *tuple-write-bits-raw-be-sample*
                                (base-prime))
  :enable (tuple-write-bits-raw-be-gadget val-env-empty-sample-holds)
  )

(define tuple-write-bits-raw-be-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "tuple_write_bits_raw_be() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (tuple-write-bits-raw-be-circuit)
            :pred tuple-write-bits-raw-be-pred
            :prime prime)

(defruled tuple-write-bits-raw-be-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (tuple-write-bits-raw-be-pred prime)
                  (r1cs::r1cs-constraints-holdp (tuple-write-bits-raw-be-gadget) nil prime)))
  :enable (tuple-write-bits-raw-be-pred tuple-write-bits-raw-be-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define to-bits-le-default-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "ToBits::to_bits_le writes into an empty vector."
  nil)

(defruled to-bits-le-default-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                t
                (r1cs::r1cs-constraints-holdp (to-bits-le-default-gadget) asg p))
           (equal (to-bits-le-funspec x)
                  (write-bits-le-impl nil x)))
  :hints (("Goal" :expand ((to-bits-le-funspec x))
                  :in-theory (enable to-bits-le-default-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled to-bits-le-default-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                t
                (equal (to-bits-le-funspec x)
                       (write-bits-le-impl nil x)))
           (r1cs::r1cs-constraints-holdp (to-bits-le-default-gadget) asg p))
  :hints (("Goal" :expand ((to-bits-le-funspec x))
                  :in-theory (enable to-bits-le-default-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *to-bits-le-default-sample* *val-env-empty-sample*)

(defruled to-bits-le-default-sample-holds
  (r1cs::r1cs-constraints-holdp (to-bits-le-default-gadget)
                                *to-bits-le-default-sample*
                                (base-prime))
  :enable (to-bits-le-default-gadget val-env-empty-sample-holds)
  )

(define to-bits-le-default-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "to_bits_le_default() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (to-bits-le-default-circuit)
            :pred to-bits-le-default-pred
            :prime prime)

(defruled to-bits-le-default-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (to-bits-le-default-pred prime)
                  (r1cs::r1cs-constraints-holdp (to-bits-le-default-gadget) nil prime)))
  :enable (to-bits-le-default-pred to-bits-le-default-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define to-bits-be-default-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "ToBits::to_bits_be writes into an empty vector."
  nil)

(defruled to-bits-be-default-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                t
                (r1cs::r1cs-constraints-holdp (to-bits-be-default-gadget) asg p))
           (equal (to-bits-be-funspec x)
                  (write-bits-be-impl nil x)))
  :hints (("Goal" :expand ((to-bits-be-funspec x))
                  :in-theory (enable to-bits-be-default-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled to-bits-be-default-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                t
                (equal (to-bits-be-funspec x)
                       (write-bits-be-impl nil x)))
           (r1cs::r1cs-constraints-holdp (to-bits-be-default-gadget) asg p))
  :hints (("Goal" :expand ((to-bits-be-funspec x))
                  :in-theory (enable to-bits-be-default-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *to-bits-be-default-sample* *val-env-empty-sample*)

(defruled to-bits-be-default-sample-holds
  (r1cs::r1cs-constraints-holdp (to-bits-be-default-gadget)
                                *to-bits-be-default-sample*
                                (base-prime))
  :enable (to-bits-be-default-gadget val-env-empty-sample-holds)
  )

(define to-bits-be-default-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "to_bits_be_default() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (to-bits-be-default-circuit)
            :pred to-bits-be-default-pred
            :prime prime)

(defruled to-bits-be-default-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (to-bits-be-default-pred prime)
                  (r1cs::r1cs-constraints-holdp (to-bits-be-default-gadget) nil prime)))
  :enable (to-bits-be-default-pred to-bits-be-default-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define to-bits-raw-le-default-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "ToBitsRaw::to_bits_raw_le writes into an empty vector."
  nil)

(defruled to-bits-raw-le-default-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                t
                (r1cs::r1cs-constraints-holdp (to-bits-raw-le-default-gadget) asg p))
           (equal (to-bits-raw-le-funspec x)
                  (write-bits-raw-le-impl nil x)))
  :hints (("Goal" :expand ((to-bits-raw-le-funspec x))
                  :in-theory (enable to-bits-raw-le-default-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled to-bits-raw-le-default-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                t
                (equal (to-bits-raw-le-funspec x)
                       (write-bits-raw-le-impl nil x)))
           (r1cs::r1cs-constraints-holdp (to-bits-raw-le-default-gadget) asg p))
  :hints (("Goal" :expand ((to-bits-raw-le-funspec x))
                  :in-theory (enable to-bits-raw-le-default-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *to-bits-raw-le-default-sample* *val-env-empty-sample*)

(defruled to-bits-raw-le-default-sample-holds
  (r1cs::r1cs-constraints-holdp (to-bits-raw-le-default-gadget)
                                *to-bits-raw-le-default-sample*
                                (base-prime))
  :enable (to-bits-raw-le-default-gadget val-env-empty-sample-holds)
  )

(define to-bits-raw-le-default-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "to_bits_raw_le_default() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (to-bits-raw-le-default-circuit)
            :pred to-bits-raw-le-default-pred
            :prime prime)

(defruled to-bits-raw-le-default-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (to-bits-raw-le-default-pred prime)
                  (r1cs::r1cs-constraints-holdp (to-bits-raw-le-default-gadget) nil prime)))
  :enable (to-bits-raw-le-default-pred to-bits-raw-le-default-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define to-bits-raw-be-default-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "ToBitsRaw::to_bits_raw_be writes into an empty vector."
  nil)

(defruled to-bits-raw-be-default-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                t
                (r1cs::r1cs-constraints-holdp (to-bits-raw-be-default-gadget) asg p))
           (equal (to-bits-raw-be-funspec x)
                  (write-bits-raw-be-impl nil x)))
  :hints (("Goal" :expand ((to-bits-raw-be-funspec x))
                  :in-theory (enable to-bits-raw-be-default-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled to-bits-raw-be-default-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                t
                (equal (to-bits-raw-be-funspec x)
                       (write-bits-raw-be-impl nil x)))
           (r1cs::r1cs-constraints-holdp (to-bits-raw-be-default-gadget) asg p))
  :hints (("Goal" :expand ((to-bits-raw-be-funspec x))
                  :in-theory (enable to-bits-raw-be-default-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *to-bits-raw-be-default-sample* *val-env-empty-sample*)

(defruled to-bits-raw-be-default-sample-holds
  (r1cs::r1cs-constraints-holdp (to-bits-raw-be-default-gadget)
                                *to-bits-raw-be-default-sample*
                                (base-prime))
  :enable (to-bits-raw-be-default-gadget val-env-empty-sample-holds)
  )

(define to-bits-raw-be-default-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "to_bits_raw_be_default() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (to-bits-raw-be-default-circuit)
            :pred to-bits-raw-be-default-pred
            :prime prime)

(defruled to-bits-raw-be-default-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (to-bits-raw-be-default-pred prime)
                  (r1cs::r1cs-constraints-holdp (to-bits-raw-be-default-gadget) nil prime)))
  :enable (to-bits-raw-be-default-pred to-bits-raw-be-default-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define vec-inject-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Vec::Inject::new maps C::new.  No constraint of its own."
  nil)

(defruled vec-inject-new-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp values)
                (r1cs::r1cs-constraints-holdp (vec-inject-new-gadget) asg p))
           (equal (inject-seq-funspec mode values)
                  (b* (((when (endp values)) nil)
                         (first (inject-impl mode (car values)))
                         ((when (reserrp first)) (spec-error))
                         (rest (inject-seq-funspec mode (cdr values)))
                         ((when (reserrp rest)) (spec-error)))
                      (cons first rest))))
  :hints (("Goal" :expand ((inject-seq-funspec mode values))
                  :in-theory (enable vec-inject-new-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled vec-inject-new-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp values)
                (equal (inject-seq-funspec mode values)
                       (b* (((when (endp values)) nil)
                         (first (inject-impl mode (car values)))
                         ((when (reserrp first)) (spec-error))
                         (rest (inject-seq-funspec mode (cdr values)))
                         ((when (reserrp rest)) (spec-error)))
                      (cons first rest))))
           (r1cs::r1cs-constraints-holdp (vec-inject-new-gadget) asg p))
  :hints (("Goal" :expand ((inject-seq-funspec mode values))
                  :in-theory (enable vec-inject-new-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *vec-inject-new-sample* *val-env-empty-sample*)

(defruled vec-inject-new-sample-holds
  (r1cs::r1cs-constraints-holdp (vec-inject-new-gadget)
                                *vec-inject-new-sample*
                                (base-prime))
  :enable (vec-inject-new-gadget val-env-empty-sample-holds)
  )

(define vec-inject-new-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "vec_inject_new() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (vec-inject-new-circuit)
            :pred vec-inject-new-pred
            :prime prime)

(defruled vec-inject-new-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (vec-inject-new-pred prime)
                  (r1cs::r1cs-constraints-holdp (vec-inject-new-gadget) nil prime)))
  :enable (vec-inject-new-pred vec-inject-new-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tuple-inject-new-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Tuple Inject::new maps each component's new.  No constraint of its own."
  nil)

(defruled tuple-inject-new-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp values)
                (r1cs::r1cs-constraints-holdp (tuple-inject-new-gadget) asg p))
           (equal (inject-seq-funspec mode values)
                  (b* (((when (endp values)) nil)
                         (first (inject-impl mode (car values)))
                         ((when (reserrp first)) (spec-error))
                         (rest (inject-seq-funspec mode (cdr values)))
                         ((when (reserrp rest)) (spec-error)))
                      (cons first rest))))
  :hints (("Goal" :expand ((inject-seq-funspec mode values))
                  :in-theory (enable tuple-inject-new-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled tuple-inject-new-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (true-listp values)
                (equal (inject-seq-funspec mode values)
                       (b* (((when (endp values)) nil)
                         (first (inject-impl mode (car values)))
                         ((when (reserrp first)) (spec-error))
                         (rest (inject-seq-funspec mode (cdr values)))
                         ((when (reserrp rest)) (spec-error)))
                      (cons first rest))))
           (r1cs::r1cs-constraints-holdp (tuple-inject-new-gadget) asg p))
  :hints (("Goal" :expand ((inject-seq-funspec mode values))
                  :in-theory (enable tuple-inject-new-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *tuple-inject-new-sample* *val-env-empty-sample*)

(defruled tuple-inject-new-sample-holds
  (r1cs::r1cs-constraints-holdp (tuple-inject-new-gadget)
                                *tuple-inject-new-sample*
                                (base-prime))
  :enable (tuple-inject-new-gadget val-env-empty-sample-holds)
  )

(define tuple-inject-new-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "tuple_inject_new() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (tuple-inject-new-circuit)
            :pred tuple-inject-new-pred
            :prime prime)

(defruled tuple-inject-new-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (tuple-inject-new-pred prime)
                  (r1cs::r1cs-constraints-holdp (tuple-inject-new-gadget) nil prime)))
  :enable (tuple-inject-new-pred tuple-inject-new-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define recursively-replace-self-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Proc-macro recursively_replace_self.  Not a circuit."
  nil)

(defruled recursively-replace-self-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (stringp replacement)
                (r1cs::r1cs-constraints-holdp (recursively-replace-self-gadget) asg p))
           (equal (recursively-replace-self-funspec stream replacement)
                  (b* (((when (atom stream)) nil)
                         (tok (car stream))
                         (new-tok
                          (cond ((and (consp tok) (eq (car tok) :ident))
                                 (if (equal (cdr tok) "self")
                                     (cons :ident replacement)
                                   tok))
                                ((and (consp tok) (eq (car tok) :group) (consp (cdr tok)))
                                 (list* :group
                                        (cadr tok)
                                        (recursively-replace-self-funspec (cddr tok)
                                                                          replacement)))
                                (t tok))))
                      (cons new-tok
                            (recursively-replace-self-funspec (cdr stream) replacement)))))
  :hints (("Goal" :expand ((recursively-replace-self-funspec stream replacement))
                  :in-theory (enable recursively-replace-self-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled recursively-replace-self-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                (stringp replacement)
                (equal (recursively-replace-self-funspec stream replacement)
                       (b* (((when (atom stream)) nil)
                         (tok (car stream))
                         (new-tok
                          (cond ((and (consp tok) (eq (car tok) :ident))
                                 (if (equal (cdr tok) "self")
                                     (cons :ident replacement)
                                   tok))
                                ((and (consp tok) (eq (car tok) :group) (consp (cdr tok)))
                                 (list* :group
                                        (cadr tok)
                                        (recursively-replace-self-funspec (cddr tok)
                                                                          replacement)))
                                (t tok))))
                      (cons new-tok
                            (recursively-replace-self-funspec (cdr stream) replacement)))))
           (r1cs::r1cs-constraints-holdp (recursively-replace-self-gadget) asg p))
  :hints (("Goal" :expand ((recursively-replace-self-funspec stream replacement))
                  :in-theory (enable recursively-replace-self-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *recursively-replace-self-sample* *val-env-empty-sample*)

(defruled recursively-replace-self-sample-holds
  (r1cs::r1cs-constraints-holdp (recursively-replace-self-gadget)
                                *recursively-replace-self-sample*
                                (base-prime))
  :enable (recursively-replace-self-gadget val-env-empty-sample-holds)
  )

(define recursively-replace-self-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "recursively_replace_self() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (recursively-replace-self-circuit)
            :pred recursively-replace-self-pred
            :prime prime)

(defruled recursively-replace-self-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (recursively-replace-self-pred prime)
                  (r1cs::r1cs-constraints-holdp (recursively-replace-self-gadget) nil prime)))
  :enable (recursively-replace-self-pred recursively-replace-self-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rename-selfs-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "Proc-macro rename_selfs renames self to _self.  Not a circuit."
  nil)

(defruled rename-selfs-gadget-sound
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                t
                (r1cs::r1cs-constraints-holdp (rename-selfs-gadget) asg p))
           (equal (rename-selfs-funspec stream)
                  (recursively-replace-self-funspec stream "_self")))
  :hints (("Goal" :expand ((rename-selfs-funspec stream))
                  :in-theory (enable rename-selfs-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defruled rename-selfs-gadget-complete
  (implies (and (equal p (base-prime))
                (r1cs::r1cs-valuationp asg p)
                t
                (equal (rename-selfs-funspec stream)
                       (recursively-replace-self-funspec stream "_self")))
           (r1cs::r1cs-constraints-holdp (rename-selfs-gadget) asg p))
  :hints (("Goal" :expand ((rename-selfs-funspec stream))
                  :in-theory (enable rename-selfs-gadget
                                     r1cs::r1cs-constraints-holdp))))

(defconst *rename-selfs-sample* *val-env-empty-sample*)

(defruled rename-selfs-sample-holds
  (r1cs::r1cs-constraints-holdp (rename-selfs-gadget)
                                *rename-selfs-sample*
                                (base-prime))
  :enable (rename-selfs-gadget val-env-empty-sample-holds)
  )

(define rename-selfs-circuit ()
  :returns (pdef pfcs::definitionp)
  (pfcs::parse-def
   "rename_selfs() := {
    }")
  ///
  (more-returns
   (pdef pfcs::sr1cs-definitionp
         :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                            pfcs::sr1cs-constraintp
                                            pfcs::r1cs-constraintp
                                            pfcs::r1cs-polynomialp
                                            pfcs::r1cs-monomialp))))))

(pfcs::lift (rename-selfs-circuit)
            :pred rename-selfs-pred
            :prime prime)

(defruled rename-selfs-pred-to-funspec
  (implies (equal prime (base-prime))
           (equal (rename-selfs-pred prime)
                  (r1cs::r1cs-constraints-holdp (rename-selfs-gadget) nil prime)))
  :enable (rename-selfs-pred rename-selfs-gadget r1cs::r1cs-constraints-holdp))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *rename-selfs-token-sample*
  '((:ident . "self")
    (:ident . "x")
    (:group :paren (:ident . "self"))))

(defruled rename-selfs-token-sample-spec
  (equal (rename-selfs-funspec *rename-selfs-token-sample*)
         '((:ident . "_self")
           (:ident . "x")
           (:group :paren (:ident . "_self"))))
  :hints (("Goal"
           :expand ((rename-selfs-funspec *rename-selfs-token-sample*)
                    (recursively-replace-self-funspec
                     '((:ident . "self")
                       (:ident . "x")
                       (:group :paren (:ident . "self")))
                     "_self")
                    (recursively-replace-self-funspec
                     '((:ident . "x")
                       (:group :paren (:ident . "self")))
                     "_self")
                    (recursively-replace-self-funspec
                     '((:group :paren (:ident . "self")))
                     "_self")
                    (recursively-replace-self-funspec
                     nil
                     "_self")
                    (recursively-replace-self-funspec
                     '((:ident . "self"))
                     "_self")
                    (recursively-replace-self-funspec nil "_self")))))
