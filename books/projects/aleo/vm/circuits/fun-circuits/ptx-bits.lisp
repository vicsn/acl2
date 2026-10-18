; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Plaintext::write_bits_le / write_bits_be, write_bits_raw_le / _be,
; to_fields, to_fields_raw, size_in_fields and num_randomizers
; (snarkVM circuit/program/src/data/plaintext/{to_bits,to_bits_raw,
; to_fields,to_fields_raw,size_in_fields,num_randomizers}.rs), by
; induction over the wire tree of ptx-tree.lisp.
;
; The only constraints are those of Literal::write_bits_le / _be on each
; leaf, in tree order.  Everything else is synthesis-time constants: the
; prefix bits, the variant (U8::constant), the size in bits (U16::constant),
; the member count (U8::constant), the element count (U32::constant), the
; member names (constant identifiers, so their size and bits are
; constants), and the bit length of each member or element
; (U16::constant of the length of its bit vector).  Field::from_bits_le
; on a chunk of at most 252 bits is a linear combination (no constraint)
; whose value is the little-endian number of the chunk, below p.
; size_in_fields computes to_bits_le (emitting its constraints) and
; returns a host u16 computed from its length.
;
; The leaf circuit is abstract (ptx-leaf-bits-*): a constraint list and
; output bit terms, sound for a leaf satisfying Literal::new
; (ptx-leaf-typed) and satisfied by the leaf witness.  It stands for the
; per-type Literal::write_bits arms; the theorems hold for every instance.
;
; Bit cache.  snarkVM stores the result of the first write_bits of each
; node in a OnceCell (one cell shared by the little- and big-endian
; orders) and returns it on later calls without new constraints.  The
; model is the first call on a plaintext with empty caches, i.e. one built
; by Plaintext::new, find on such a plaintext, or from_bit_array.  On a
; plaintext built by from_bits the cache holds the raw input bits instead;
; that case is the README limitation and is not covered here.

(in-package "ALEOVM")

(include-book "ptx-tree")

(set-verify-guards-eagerness 0)

(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Leaf interface: Literal::write_bits_le / _be.

(defconst *ptx-false-constraint*
  (r1cs::make-r1cs-constraint :a nil :b nil :c '((1 1))))

(encapsulate
  (((ptx-leaf-bits-gadget * *) => *)
   ((ptx-leaf-bits-out * *) => *)
   ((ptx-leaf-bits-witnessp * * * *) => *))

  (local (defun ptx-leaf-bits-gadget (w bigp)
           (declare (ignore w bigp))
           (list *ptx-false-constraint*)))
  (local (defun ptx-leaf-bits-out (w bigp) (declare (ignore w bigp)) nil))
  (local (defun ptx-leaf-bits-witnessp (w bigp asg p)
           (declare (ignore w bigp asg p))
           nil))

  (defruled ptx-leaf-bits-sound
    (implies (and (primep p)
                  (ptx-leaf-typed w asg)
                  (r1cs::r1cs-constraints-holdp (ptx-leaf-bits-gadget w bigp)
                                                asg p))
             (equal (ptx-terms-val (ptx-leaf-bits-out w bigp) asg)
                    (if bigp
                        (literal-to-bits-be (ptx-leaf-val w asg))
                      (literal-to-bits-le (ptx-leaf-val w asg)))))
    :enable (r1cs::r1cs-constraint-holdsp r1cs::dot-product primep)
    :prep-lemmas
    ((defrule mod-1-when-big
       (implies (and (integerp p) (<= 2 p))
                (equal (mod 1 p) 1))
       :enable mod)))

  (defruled ptx-leaf-bits-complete
    (implies (and (primep p)
                  (ptx-leaf-typed w asg)
                  (ptx-leaf-bits-witnessp w bigp asg p))
             (r1cs::r1cs-constraints-holdp (ptx-leaf-bits-gadget w bigp)
                                           asg p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; write_bits_le / write_bits_be.

(defines ptx-bits-out
  :flag-local nil
  :short "The output bit terms of Plaintext::write_bits_le (@('bigp') nil)
          or write_bits_be."

  (define ptx-bits-out (wt bigp)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (append (list 0 1)
                       (values-uint-to-bits (len (cdr wt)) 8 bigp)
                       (ptx-mbits-out (cdr wt) bigp)))
      (:array (append (list 1 0)
                      (values-uint-to-bits (len (cdr wt)) 32 bigp)
                      (ptx-lbits-out (cdr wt) bigp)))
      (otherwise (append (list 0 0)
                         (values-uint-to-bits (ptx-leaf-variant (cdr wt)) 8 bigp)
                         (values-uint-to-bits (ptx-leaf-size (cdr wt)) 16 bigp)
                         (ptx-leaf-bits-out (cdr wt) bigp)))))

  (define ptx-mbits-out (wms bigp)
    :measure (acl2-count wms)
    (if (atom wms)
        nil
      (b* ((name (identifier-fix (car (car wms))))
           (value-bits (ptx-bits-out (cdr (car wms)) bigp)))
        (append (values-uint-to-bits (identifier-size-in-bits name) 8 bigp)
                (values-identifier-to-bits name bigp)
                (values-uint-to-bits (len value-bits) 16 bigp)
                value-bits
                (ptx-mbits-out (cdr wms) bigp)))))

  (define ptx-lbits-out (wts bigp)
    :measure (acl2-count wts)
    (if (atom wts)
        nil
      (b* ((value-bits (ptx-bits-out (car wts) bigp)))
        (append (values-uint-to-bits (len value-bits) 16 bigp)
                value-bits
                (ptx-lbits-out (cdr wts) bigp))))))

(defines ptx-bits-gadget
  :flag-local nil
  :short "The constraints of Plaintext::write_bits_le / _be: those of the
          leaves, in order."

  (define ptx-bits-gadget (wt bigp)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (ptx-mbits-gadget (cdr wt) bigp))
      (:array (ptx-lbits-gadget (cdr wt) bigp))
      (otherwise (ptx-leaf-bits-gadget (cdr wt) bigp))))

  (define ptx-mbits-gadget (wms bigp)
    :measure (acl2-count wms)
    (if (atom wms)
        nil
      (append (ptx-bits-gadget (cdr (car wms)) bigp)
              (ptx-mbits-gadget (cdr wms) bigp))))

  (define ptx-lbits-gadget (wts bigp)
    :measure (acl2-count wts)
    (if (atom wts)
        nil
      (append (ptx-bits-gadget (car wts) bigp)
              (ptx-lbits-gadget (cdr wts) bigp)))))

(defines ptx-bits-witnessp
  :flag-local nil
  :short "Every leaf carries the witness of its Literal::write_bits."

  (define ptx-bits-witnessp (wt bigp asg p)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (ptx-mbits-witnessp (cdr wt) bigp asg p))
      (:array (ptx-lbits-witnessp (cdr wt) bigp asg p))
      (otherwise (and (ptx-leaf-bits-witnessp (cdr wt) bigp asg p) t))))

  (define ptx-mbits-witnessp (wms bigp asg p)
    :measure (acl2-count wms)
    (if (atom wms)
        t
      (and (ptx-bits-witnessp (cdr (car wms)) bigp asg p)
           (ptx-mbits-witnessp (cdr wms) bigp asg p))))

  (define ptx-lbits-witnessp (wts bigp asg p)
    :measure (acl2-count wts)
    (if (atom wts)
        t
      (and (ptx-bits-witnessp (car wts) bigp asg p)
           (ptx-lbits-witnessp (cdr wts) bigp asg p)))))

(local (in-theory (disable values-uint-to-bits)))

(defsection ptx-funspec-openers
  :short "The bit funspecs on constructor terms."

  (defruled ptx-to-bits-of-literal
    (implies (and (literalp l))
    (equal (values-plaintext-to-bits (plaintext-literal l) bigp)
           (append (list 0 0)
                   (values-uint-to-bits (literal-variant l) 8 bigp)
                   (values-uint-to-bits (literal-size-in-bits l) 16 bigp)
                   (if bigp (literal-to-bits-be l) (literal-to-bits-le l)))))
    :expand ((values-plaintext-to-bits (plaintext-literal l) bigp)))

  (defruled ptx-to-bits-of-struct
    (implies (and (plaintext-member-listp ms))
    (equal (values-plaintext-to-bits (plaintext-struct ms) bigp)
           (append (list 0 1)
                   (values-uint-to-bits (len ms) 8 bigp)
                   (values-plaintext-members-to-bits ms bigp))))
    :expand ((values-plaintext-to-bits (plaintext-struct ms) bigp)))

  (defruled ptx-to-bits-of-array
    (implies (and (plaintext-listp es))
    (equal (values-plaintext-to-bits (plaintext-array es) bigp)
           (append (list 1 0)
                   (values-uint-to-bits (len es) 32 bigp)
                   (values-plaintext-elements-to-bits es bigp))))
    :expand ((values-plaintext-to-bits (plaintext-array es) bigp)))

  (defruled ptx-members-to-bits-of-cons
    (implies (and (plaintext-memberp m) (plaintext-member-listp ms))
    (equal (values-plaintext-members-to-bits (cons m ms) bigp)
           (b* ((name (plaintext-member->name m))
                (value-bits (values-plaintext-to-bits (plaintext-member->value m) bigp)))
             (append (values-uint-to-bits (identifier-size-in-bits name) 8 bigp)
                     (values-identifier-to-bits name bigp)
                     (values-uint-to-bits (len value-bits) 16 bigp)
                     value-bits
                     (values-plaintext-members-to-bits ms bigp)))))
    :expand ((values-plaintext-members-to-bits (cons m ms) bigp)))

  (defruled ptx-members-to-bits-of-nil
    (equal (values-plaintext-members-to-bits nil bigp) nil)
    :expand ((values-plaintext-members-to-bits nil bigp)))

  (defruled ptx-elements-to-bits-of-cons
    (implies (and (plaintextp e) (plaintext-listp es))
    (equal (values-plaintext-elements-to-bits (cons e es) bigp)
           (b* ((value-bits (values-plaintext-to-bits e bigp)))
             (append (values-uint-to-bits (len value-bits) 16 bigp)
                     value-bits
                     (values-plaintext-elements-to-bits es bigp)))))
    :expand ((values-plaintext-elements-to-bits (cons e es) bigp)))

  (defruled ptx-elements-to-bits-of-nil
    (equal (values-plaintext-elements-to-bits nil bigp) nil)
    :expand ((values-plaintext-elements-to-bits nil bigp)))

  (defruled ptx-to-bits-raw-of-literal
    (implies (and (literalp l))
    (equal (values-plaintext-to-bits-raw (plaintext-literal l) bigp)
           (if bigp (literal-to-bits-be l) (literal-to-bits-le l))))
    :expand ((values-plaintext-to-bits-raw (plaintext-literal l) bigp)))

  (defruled ptx-to-bits-raw-of-struct
    (implies (and (plaintext-member-listp ms))
    (equal (values-plaintext-to-bits-raw (plaintext-struct ms) bigp)
           (values-plaintext-members-to-bits-raw ms bigp)))
    :expand ((values-plaintext-to-bits-raw (plaintext-struct ms) bigp)))

  (defruled ptx-to-bits-raw-of-array
    (implies (and (plaintext-listp es))
    (equal (values-plaintext-to-bits-raw (plaintext-array es) bigp)
           (values-plaintext-elements-to-bits-raw es bigp)))
    :expand ((values-plaintext-to-bits-raw (plaintext-array es) bigp)))

  (defruled ptx-members-to-bits-raw-of-cons
    (implies (and (plaintext-memberp m) (plaintext-member-listp ms))
    (equal (values-plaintext-members-to-bits-raw (cons m ms) bigp)
           (append (values-plaintext-to-bits-raw (plaintext-member->value m) bigp)
                   (values-plaintext-members-to-bits-raw ms bigp))))
    :expand ((values-plaintext-members-to-bits-raw (cons m ms) bigp)))

  (defruled ptx-members-to-bits-raw-of-nil
    (equal (values-plaintext-members-to-bits-raw nil bigp) nil)
    :expand ((values-plaintext-members-to-bits-raw nil bigp)))

  (defruled ptx-elements-to-bits-raw-of-cons
    (implies (and (plaintextp e) (plaintext-listp es))
    (equal (values-plaintext-elements-to-bits-raw (cons e es) bigp)
           (append (values-plaintext-to-bits-raw e bigp)
                   (values-plaintext-elements-to-bits-raw es bigp))))
    :expand ((values-plaintext-elements-to-bits-raw (cons e es) bigp)))

  (defruled ptx-elements-to-bits-raw-of-nil
    (equal (values-plaintext-elements-to-bits-raw nil bigp) nil)
    :expand ((values-plaintext-elements-to-bits-raw nil bigp))))

(local (in-theory (enable ptx-to-bits-of-literal ptx-to-bits-of-struct
                          ptx-to-bits-of-array ptx-members-to-bits-of-cons
                          ptx-members-to-bits-of-nil ptx-elements-to-bits-of-cons
                          ptx-elements-to-bits-of-nil ptx-to-bits-raw-of-literal
                          ptx-to-bits-raw-of-struct ptx-to-bits-raw-of-array
                          ptx-members-to-bits-raw-of-cons
                          ptx-members-to-bits-raw-of-nil
                          ptx-elements-to-bits-raw-of-cons
                          ptx-elements-to-bits-raw-of-nil)))

(defthm-ptx-bits-out-flag
  (defthm ptx-bits-out-sound
    (implies (and (primep p)
                  (ptx-typed wt asg)
                  (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt bigp) asg p))
             (equal (ptx-terms-val (ptx-bits-out wt bigp) asg)
                    (values-plaintext-to-bits (ptx-val wt asg) bigp)))
    :flag ptx-bits-out)
  (defthm ptx-mbits-out-sound
    (implies (and (primep p)
                  (ptx-mtyped wms asg)
                  (r1cs::r1cs-constraints-holdp (ptx-mbits-gadget wms bigp) asg p))
             (equal (ptx-terms-val (ptx-mbits-out wms bigp) asg)
                    (values-plaintext-members-to-bits (ptx-mval wms asg) bigp)))
    :flag ptx-mbits-out)
  (defthm ptx-lbits-out-sound
    (implies (and (primep p)
                  (ptx-ltyped wts asg)
                  (r1cs::r1cs-constraints-holdp (ptx-lbits-gadget wts bigp) asg p))
             (equal (ptx-terms-val (ptx-lbits-out wts bigp) asg)
                    (values-plaintext-elements-to-bits (ptx-lval wts asg) bigp)))
    :flag ptx-lbits-out)
  :hints (("Goal"
           :in-theory (enable ptx-leaf-bits-sound
                              ptx-leaf-variant-correct
                              ptx-leaf-size-correct)
           :expand ((ptx-bits-out wt bigp)
                    (ptx-mbits-out wms bigp)
                    (ptx-lbits-out wts bigp)
                    (ptx-bits-gadget wt bigp)
                    (ptx-mbits-gadget wms bigp)
                    (ptx-lbits-gadget wts bigp)
                    (ptx-typed wt asg)
                    (ptx-mtyped wms asg)
                    (ptx-ltyped wts asg)
                    (ptx-val wt asg)
                    (ptx-mval wms asg)
                    (ptx-lval wts asg)))))

(defthm-ptx-bits-gadget-flag
  (defthm ptx-bits-gadget-complete
    (implies (and (primep p)
                  (ptx-typed wt asg)
                  (ptx-bits-witnessp wt bigp asg p))
             (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt bigp) asg p))
    :flag ptx-bits-gadget)
  (defthm ptx-mbits-gadget-complete
    (implies (and (primep p)
                  (ptx-mtyped wms asg)
                  (ptx-mbits-witnessp wms bigp asg p))
             (r1cs::r1cs-constraints-holdp (ptx-mbits-gadget wms bigp) asg p))
    :flag ptx-mbits-gadget)
  (defthm ptx-lbits-gadget-complete
    (implies (and (primep p)
                  (ptx-ltyped wts asg)
                  (ptx-lbits-witnessp wts bigp asg p))
             (r1cs::r1cs-constraints-holdp (ptx-lbits-gadget wts bigp) asg p))
    :flag ptx-lbits-gadget)
  :hints (("Goal"
           :in-theory (enable ptx-leaf-bits-complete)
           :expand ((ptx-bits-gadget wt bigp)
                    (ptx-mbits-gadget wms bigp)
                    (ptx-lbits-gadget wts bigp)
                    (ptx-typed wt asg)
                    (ptx-mtyped wms asg)
                    (ptx-ltyped wts asg)
                    (ptx-bits-witnessp wt bigp asg p)
                    (ptx-mbits-witnessp wms bigp asg p)
                    (ptx-lbits-witnessp wts bigp asg p)))))

(defruled ptx-write-bits-le-sound
  :short "R1CS-SOUND of Plaintext::write_bits_le, given Literal::new on each
          leaf: the output terms evaluate to the funspec of the plaintext
          the input wires denote."
  (implies (and (primep p)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt nil) asg p))
           (and (plaintextp (ptx-val wt asg))
                (equal (ptx-terms-val (ptx-bits-out wt nil) asg)
                       (plaintext-to-bits-le (ptx-val wt asg)))))
  :enable plaintext-to-bits-le)

(defruled ptx-write-bits-be-sound
  (implies (and (primep p)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt t) asg p))
           (and (plaintextp (ptx-val wt asg))
                (equal (ptx-terms-val (ptx-bits-out wt t) asg)
                       (plaintext-to-bits-be (ptx-val wt asg)))))
  :enable plaintext-to-bits-be)

(defruled ptx-write-bits-complete
  :short "R1CS-COMPLETE of Plaintext::write_bits_le / _be: with the leaf
          witnesses the constraints hold and the output is the funspec's."
  (implies (and (primep p)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (ptx-bits-witnessp wt bigp asg p))
           (and (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt bigp) asg p)
                (equal (ptx-terms-val (ptx-bits-out wt bigp) asg)
                       (values-plaintext-to-bits (ptx-val wt asg) bigp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; write_bits_raw_le / write_bits_raw_be: the leaf bits only.
;; The constraints are the same leaf constraints, in the same order.

(defines ptx-raw-out
  :flag-local nil

  (define ptx-raw-out (wt bigp)
    :measure (acl2-count wt)
    (case (car wt)
      (:struct (ptx-mraw-out (cdr wt) bigp))
      (:array (ptx-lraw-out (cdr wt) bigp))
      (otherwise (ptx-leaf-bits-out (cdr wt) bigp))))

  (define ptx-mraw-out (wms bigp)
    :measure (acl2-count wms)
    (if (atom wms)
        nil
      (append (ptx-raw-out (cdr (car wms)) bigp)
              (ptx-mraw-out (cdr wms) bigp))))

  (define ptx-lraw-out (wts bigp)
    :measure (acl2-count wts)
    (if (atom wts)
        nil
      (append (ptx-raw-out (car wts) bigp)
              (ptx-lraw-out (cdr wts) bigp)))))

(defthm-ptx-raw-out-flag
  (defthm ptx-raw-out-sound
    (implies (and (primep p)
                  (ptx-typed wt asg)
                  (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt bigp) asg p))
             (equal (ptx-terms-val (ptx-raw-out wt bigp) asg)
                    (values-plaintext-to-bits-raw (ptx-val wt asg) bigp)))
    :flag ptx-raw-out)
  (defthm ptx-mraw-out-sound
    (implies (and (primep p)
                  (ptx-mtyped wms asg)
                  (r1cs::r1cs-constraints-holdp (ptx-mbits-gadget wms bigp) asg p))
             (equal (ptx-terms-val (ptx-mraw-out wms bigp) asg)
                    (values-plaintext-members-to-bits-raw (ptx-mval wms asg) bigp)))
    :flag ptx-mraw-out)
  (defthm ptx-lraw-out-sound
    (implies (and (primep p)
                  (ptx-ltyped wts asg)
                  (r1cs::r1cs-constraints-holdp (ptx-lbits-gadget wts bigp) asg p))
             (equal (ptx-terms-val (ptx-lraw-out wts bigp) asg)
                    (values-plaintext-elements-to-bits-raw (ptx-lval wts asg) bigp)))
    :flag ptx-lraw-out)
  :hints (("Goal"
           :in-theory (enable ptx-leaf-bits-sound)
           :expand ((ptx-raw-out wt bigp)
                    (ptx-mraw-out wms bigp)
                    (ptx-lraw-out wts bigp)
                    (ptx-bits-gadget wt bigp)
                    (ptx-mbits-gadget wms bigp)
                    (ptx-lbits-gadget wts bigp)
                    (ptx-typed wt asg)
                    (ptx-mtyped wms asg)
                    (ptx-ltyped wts asg)
                    (ptx-val wt asg)
                    (ptx-mval wms asg)
                    (ptx-lval wts asg)))))

(defruled ptx-write-bits-raw-le-sound
  (implies (and (primep p)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt nil) asg p))
           (and (plaintextp (ptx-val wt asg))
                (equal (ptx-terms-val (ptx-raw-out wt nil) asg)
                       (plaintext-to-bits-raw-le (ptx-val wt asg)))))
  :enable plaintext-to-bits-raw-le)

(defruled ptx-write-bits-raw-be-sound
  (implies (and (primep p)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt t) asg p))
           (and (plaintextp (ptx-val wt asg))
                (equal (ptx-terms-val (ptx-raw-out wt t) asg)
                       (plaintext-to-bits-raw-be (ptx-val wt asg)))))
  :enable plaintext-to-bits-raw-be)

(defruled ptx-write-bits-raw-complete
  (implies (and (primep p)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (ptx-bits-witnessp wt bigp asg p))
           (and (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt bigp) asg p)
                (equal (ptx-terms-val (ptx-raw-out wt bigp) asg)
                       (values-plaintext-to-bits-raw (ptx-val wt asg) bigp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Packing into fields: bits.chunks(252).map(Field::from_bits_le).
;; Each output field is the linear combination sum_i 2^i b_i of its chunk.

(define ptx-chunks (terms)
  :short "The chunks of at most 252 bit terms; each is one output field."
  :measure (len terms)
  (if (atom terms)
      nil
    (cons (take (min (len terms) 252) terms)
          (ptx-chunks (nthcdr 252 terms))))
  ///
  (defrule ptx-len-of-chunks
    (equal (len (ptx-chunks terms))
           (len (values-pack-bits (ptx-terms-val terms asg))))
    :induct (ptx-chunks terms)
    :expand ((values-pack-bits (ptx-terms-val terms asg)))
    :enable (ptx-terms-val)))

(define ptx-chunks-val (chunks asg)
  :short "The values of the output linear combinations."
  (if (atom chunks)
      nil
    (cons (lebits=>nat (ptx-terms-val (car chunks) asg))
          (ptx-chunks-val (cdr chunks) asg))))

(defrule ptx-chunks-val-correct
  (implies (bit-listp (ptx-terms-val terms asg))
           (equal (ptx-chunks-val (ptx-chunks terms) asg)
                  (values-pack-bits (ptx-terms-val terms asg))))
  :induct (ptx-chunks terms)
  :expand ((values-pack-bits (ptx-terms-val terms asg))
           (ptx-chunks terms)
           (:free (x y) (ptx-chunks-val (cons x y) asg))
           (ptx-chunks-val nil asg))
  :enable (ptx-chunks ptx-terms-val))

(define ptx-to-fields-out (terms)
  :short "The fields of a bit vector, or @(':error') where snarkVM halts
          (more than MAX_DATA_SIZE_IN_FIELDS fields)."
  (b* ((chunks (ptx-chunks terms)))
    (if (<= (len chunks) (values-max-data-size-in-fields))
        chunks
      :error)))

(defruled ptx-to-fields-out-correct
  (implies (bit-listp (ptx-terms-val terms asg))
           (b* ((out (ptx-to-fields-out terms))
                (spec (values-pack-bits-bounded (ptx-terms-val terms asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-chunks-val out asg) spec)))))
  :enable (ptx-to-fields-out values-pack-bits-bounded spec-error))

(defruled ptx-to-fields-sound
  :short "R1CS-SOUND of Plaintext::to_fields, given Literal::new on each
          leaf.  The constraints are those of write_bits_le."
  (implies (and (primep p)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt nil) asg p))
           (b* ((out (ptx-to-fields-out (append (ptx-bits-out wt nil) (list 1))))
                (spec (plaintext-to-fields (ptx-val wt asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-chunks-val out asg) spec)))))
  :use ((:instance ptx-to-fields-out-correct
         (terms (append (ptx-bits-out wt nil) (list 1)))))
  :enable (plaintext-to-fields ptx-write-bits-le-sound plaintext-to-bits-le))

(defruled ptx-to-fields-raw-sound
  (implies (and (primep p)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt nil) asg p))
           (b* ((out (ptx-to-fields-out (ptx-raw-out wt nil)))
                (spec (plaintext-to-fields-raw (ptx-val wt asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-chunks-val out asg) spec)))))
  :use ((:instance ptx-to-fields-out-correct
         (terms (ptx-raw-out wt nil))))
  :enable (plaintext-to-fields-raw plaintext-to-bits-raw-le))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; size_in_fields and num_randomizers: a host value from the length of
;; to_bits_le, whose constraints (ptx-bits-gadget wt nil) are emitted.

(define ptx-size-in-fields (wt)
  (b* ((num-bits (+ (len (ptx-bits-out wt nil)) 1))
       (num-fields (ceiling num-bits 252)))
    (if (<= num-fields (values-max-data-size-in-fields))
        num-fields
      :error)))

(defruled ptx-size-in-fields-sound
  (implies (and (primep p)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt nil) asg p))
           (b* ((out (ptx-size-in-fields wt))
                (spec (plaintext-size-in-fields (ptx-val wt asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :use ((:instance ptx-write-bits-le-sound)
        (:instance ptx-len-of-terms-val (xs (ptx-bits-out wt nil))))
  :disable ptx-len-of-terms-val
  :enable (ptx-size-in-fields plaintext-size-in-fields spec-error))

(defruled ptx-num-randomizers-sound
  (implies (and (primep p)
                (ptx-wtp wt)
                (ptx-typed wt asg)
                (r1cs::r1cs-constraints-holdp (ptx-bits-gadget wt nil) asg p))
           (b* ((out (ptx-size-in-fields wt))
                (spec (plaintext-num-randomizers (ptx-val wt asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :use ptx-size-in-fields-sound
  :enable plaintext-num-randomizers)
