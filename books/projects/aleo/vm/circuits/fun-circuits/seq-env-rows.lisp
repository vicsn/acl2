; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The environment-crate rows over generic element types:
;
;   write_bits_{le,be,raw_le,raw_be} for Vec<C>, [C; N], &[C] and tuples
;   (circuit/environment/src/traits/to_bits.rs), the to_bits_* trait
;   defaults, and Inject::new for Vec<C> and tuples (inject.rs).
;
; The funspecs (fun-specs/primitives-environment.lisp) are stated over
; the abstract element functions write-bits-*-impl and inject-impl.  Here
; each element kind gets an abstract element circuit (an encapsulate)
; whose soundness and completeness are stated against that same abstract
; funspec, and seq-framework is instantiated with it.  The resulting
; theorems hold for every element circuit satisfying those properties,
; which is the meaning of the R1CS-SOUND-IF / R1CS-COMPLETE-IF condition.
;
; snarkVM emits nothing for these functions: Vec and arrays delegate to
; the slice, the slice and tuple impls call the element write in order on
; one accumulator, and to_bits_* calls write_bits_* on an empty vector.
; The container circuit is therefore the concatenation of the element
; circuits, each on its own wires (blocks), plus the shared wires.  A
; tuple is the heterogeneous case: the type tag of each block selects the
; element circuit.

(in-package "ALEOVM")

(include-book "seq-framework")

(local (in-theory (disable base-prime (:e base-prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro seq-def-write-kind (k impl seqfun tobits)
  (let* ((wiresp (seq-mk-name k "-WIRESP"))
         (valp (seq-mk-name k "-VALP"))
         (gadget (seq-mk-name k "-ELEM-GADGET"))
         (in (seq-mk-name k "-IN"))
         (out (seq-mk-name k "-OUT"))
         (witness (seq-mk-name k "-ELEM-WITNESS"))
         (espec (seq-mk-name k "-ELEM-SPEC"))
         (sspec (seq-mk-name k "-SEQ-SPEC"))
         (extends (seq-mk-name impl "-EXTENDS-ACCUMULATOR"))
         (bitl (intern-in-package-of-symbol
                (concatenate 'string "BIT-LISTP-OF-" (symbol-name impl)) impl)))
    `(progn
       (encapsulate
         (((,wiresp * *) => *)
          ((,valp * *) => *)
          ((,gadget * *) => *)
          ((,in * * *) => *)
          ((,out * * *) => *)
          ((,witness * * *) => *))

         (local (defun ,wiresp (ty wires) (declare (ignore ty)) (null wires)))
         (local (defun ,valp (ty x) (declare (ignore ty)) (equal x 0)))
         (local (defun ,gadget (ty wires) (declare (ignore ty wires)) nil))
         (local (defun ,in (ty wires asg) (declare (ignore ty wires asg)) 0))
         (local (defun ,out (ty wires asg)
                  (declare (ignore ty wires asg))
                  (,impl nil 0)))
         (local (defun ,witness (ty wires x)
                  (declare (ignore ty wires x))
                  nil))
         (local (defthm true-listp-when-bit-listp
                  (implies (bit-listp x) (true-listp x))))
         (local (defthm bit-listp-0
                  (bit-listp (,impl nil 0))
                  :hints (("Goal" :use ((:instance ,bitl (acc nil) (x 0)))))))

         (defthm ,(seq-mk-name k "-WIRESP-NECC")
           (implies (,wiresp ty wires)
                    (and (symbol-listp wires)
                         (no-duplicatesp-equal wires))))

         (defthm ,(seq-mk-name k "-TRUE-LISTP-OF-OUT")
           (true-listp (,out ty wires asg)))

         (defthm ,(seq-mk-name k "-WITNESS-PROPS")
           (implies (and (,wiresp ty wires)
                         (,valp ty x))
                    (and (r1cs::r1cs-valuationp (,witness ty wires x)
                                                (base-prime))
                         (equal (strip-cars (,witness ty wires x)) wires))))

         (defthm ,(seq-mk-name k "-ALISTP-OF-WITNESS")
           (implies (and (,wiresp ty wires)
                         (,valp ty x))
                    (alistp (,witness ty wires x))))

         (defthm ,(seq-mk-name k "-ELEM-SOUND")
           (implies (and (,wiresp ty wires)
                         (r1cs::r1cs-valuationp asg (base-prime))
                         (r1cs::valuation-binds-allp asg wires)
                         (seq-shared-ok asg)
                         (r1cs::r1cs-constraints-holdp (,gadget ty wires)
                                                       asg (base-prime)))
                    (and (,valp ty (,in ty wires asg))
                         (equal (,impl acc (,in ty wires asg))
                                (append acc (,out ty wires asg)))))
           :hints (("Goal" :use ((:instance ,extends (x 0))))))

         (defthm ,(seq-mk-name k "-ELEM-COMPLETE")
           (implies (and (,wiresp ty wires)
                         (,valp ty x)
                         (r1cs::r1cs-valuationp asg (base-prime))
                         (seq-shared-ok asg)
                         (seq-agree wires asg (,witness ty wires x)))
                    (and (r1cs::r1cs-constraints-holdp (,gadget ty wires)
                                                       asg (base-prime))
                         (equal (,in ty wires asg) x)))))

       (defun ,espec (ty acc x)
         (declare (ignore ty))
         (,impl acc x))

       (defun ,sspec (tys acc xs)
         (declare (ignore tys))
         (,seqfun acc (true-list-fix xs)))

       (seq-instantiate-write-bits
        ,k
        :wiresp ,wiresp :valp ,valp :gadget ,gadget :in ,in :out ,out
        :spec ,espec :witness ,witness :spec-seq ,sspec
        :theory (enable ,espec ,sspec ,seqfun true-list-fix
                         ,(seq-mk-name k "-ELEM-SOUND")
                         ,(seq-mk-name k "-ELEM-COMPLETE")
                         ,(seq-mk-name k "-WITNESS-PROPS")
                         ,(seq-mk-name k "-ALISTP-OF-WITNESS")
                         ,(seq-mk-name k "-TRUE-LISTP-OF-OUT")
                         ,(seq-mk-name k "-WIRESP-NECC")
                         ,(seq-mk-name k "-BLOCKS-WIRESP")
                         ,(seq-mk-name k "-GADGET")
                         ,(seq-mk-name k "-INS")
                         ,(seq-mk-name k "-OUTS")
                         ,(seq-mk-name k "-VALSP")
                         ,(seq-mk-name k "-WITNESS")
                         ,(seq-mk-name k "-BLOCKS-DISJOINTP")
                         ))

       ;; Container rows, stated against the row funspec.

       (defruled ,(seq-mk-name k "-CONTAINER-SOUND")
         (implies (and (,(seq-mk-name k "-BLOCKS-WIRESP") blocks)
                       (true-listp acc)
                       (r1cs::r1cs-valuationp asg (base-prime))
                       (r1cs::valuation-binds-allp asg (seq-blocks-wires blocks))
                       (seq-shared-ok asg)
                       (r1cs::r1cs-constraints-holdp
                        (,(seq-mk-name k "-GADGET") blocks) asg (base-prime)))
                  (and (,(seq-mk-name k "-VALSP") (seq-blocks-tys blocks)
                        (,(seq-mk-name k "-INS") blocks asg))
                       (equal (,seqfun acc (,(seq-mk-name k "-INS") blocks asg))
                              (append acc (,(seq-mk-name k "-OUTS") blocks asg)))))
         :use ((:instance ,(seq-mk-name k "-GADGET-SOUND")))
         :prep-lemmas
         ((defrule true-listp-of-ins
            (true-listp (,(seq-mk-name k "-INS") blocks asg)))))

       (defruled ,(seq-mk-name k "-CONTAINER-COMPLETE")
         (implies (and (,(seq-mk-name k "-BLOCKS-WIRESP") blocks)
                       (,(seq-mk-name k "-BLOCKS-DISJOINTP") blocks)
                       (true-listp acc)
                       (,(seq-mk-name k "-VALSP") (seq-blocks-tys blocks) xs))
                  (b* ((asg (,(seq-mk-name k "-WITNESS") blocks xs)))
                    (and (r1cs::r1cs-valuationp asg (base-prime))
                         (r1cs::valuation-binds-allp asg (seq-blocks-wires blocks))
                         (seq-shared-ok asg)
                         (r1cs::r1cs-constraints-holdp
                          (,(seq-mk-name k "-GADGET") blocks) asg (base-prime))
                         (equal (,(seq-mk-name k "-INS") blocks asg) xs)
                         (equal (append acc (,(seq-mk-name k "-OUTS") blocks asg))
                                (,seqfun acc xs)))))
         :use ((:instance ,(seq-mk-name k "-GADGET-COMPLETE")))
         :prep-lemmas
         ((defrule true-listp-when-valsp
            (implies (,(seq-mk-name k "-VALSP") tys xs)
                     (true-listp xs)))))

       ;; Trait default to_bits_*: write_bits_* into an empty vector.

       (defruled ,(seq-mk-name k "-TO-BITS-SOUND")
         (implies (and (,wiresp ty wires)
                       (r1cs::r1cs-valuationp asg (base-prime))
                       (r1cs::valuation-binds-allp asg wires)
                       (seq-shared-ok asg)
                       (r1cs::r1cs-constraints-holdp (,gadget ty wires)
                                                     asg (base-prime)))
                  (and (,valp ty (,in ty wires asg))
                       (equal (,tobits (,in ty wires asg))
                              (,out ty wires asg))))
         :enable ,tobits
         :use ((:instance ,(seq-mk-name k "-ELEM-SOUND") (acc nil))))

       (defruled ,(seq-mk-name k "-TO-BITS-COMPLETE")
         (implies (and (,wiresp ty wires)
                       (,valp ty x)
                       (r1cs::r1cs-valuationp asg (base-prime))
                       (r1cs::valuation-binds-allp asg wires)
                       (seq-shared-ok asg)
                       (seq-agree wires asg (,witness ty wires x)))
                  (and (r1cs::r1cs-constraints-holdp (,gadget ty wires)
                                                     asg (base-prime))
                       (equal (,out ty wires asg) (,tobits x))))
         :enable ,tobits
         :use ((:instance ,(seq-mk-name k "-ELEM-COMPLETE"))
               (:instance ,(seq-mk-name k "-ELEM-SOUND") (acc nil)))))))

(seq-def-write-kind seq-le write-bits-le-impl
  write-bits-le-seq-funspec to-bits-le-funspec)
(seq-def-write-kind seq-be write-bits-be-impl
  write-bits-be-seq-funspec to-bits-be-funspec)
(seq-def-write-kind seq-raw-le write-bits-raw-le-impl
  write-bits-raw-le-seq-funspec to-bits-raw-le-funspec)
(seq-def-write-kind seq-raw-be write-bits-raw-be-impl
  write-bits-raw-be-seq-funspec to-bits-raw-be-funspec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inject::new for Vec<C> and tuples, over an abstract element circuit for
;; the abstract element funspec inject-impl, in a variable mode.

(encapsulate
  (((seq-ij-wiresp * *) => *)
   ((seq-ij-elem-gadget * *) => *)
   ((seq-ij-out * * *) => *)
   ((seq-ij-elem-witness * * *) => *))

  (local (defun seq-ij-wiresp (ty wires) (declare (ignore ty wires)) nil))
  (local (defun seq-ij-elem-gadget (ty wires) (declare (ignore ty wires)) nil))
  (local (defun seq-ij-out (ty wires asg) (declare (ignore ty wires asg)) 0))
  (local (defun seq-ij-elem-witness (ty wires v)
           (declare (ignore ty wires v))
           nil))

  (defthm seq-ij-wiresp-necc
    (implies (seq-ij-wiresp ty wires)
             (and (symbol-listp wires)
                  (no-duplicatesp-equal wires))))

  (defthm seq-ij-witness-props
    (implies (and (seq-ij-wiresp ty wires)
                  (not (reserrp (inject-impl mode v)))
                  (member-equal mode '(:public :private)))
             (and (r1cs::r1cs-valuationp (seq-ij-elem-witness ty wires v)
                                         (base-prime))
                  (equal (strip-cars (seq-ij-elem-witness ty wires v)) wires))))

  (defthm seq-ij-alistp-of-witness
    (implies (and (seq-ij-wiresp ty wires)
                  (not (reserrp (inject-impl mode v)))
                  (member-equal mode '(:public :private)))
             (alistp (seq-ij-elem-witness ty wires v))))

  (defthm seq-ij-elem-sound
    (implies (and (seq-ij-wiresp ty wires)
                  (member-equal mode '(:public :private))
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-binds-allp asg wires)
                  (seq-shared-ok asg)
                  (r1cs::r1cs-constraints-holdp (seq-ij-elem-gadget ty wires)
                                                asg (base-prime)))
             (equal (inject-impl mode (seq-ij-out ty wires asg))
                    (seq-ij-out ty wires asg))))

  (defthm seq-ij-elem-sound-not-error
    (implies (and (seq-ij-wiresp ty wires)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-binds-allp asg wires)
                  (seq-shared-ok asg)
                  (r1cs::r1cs-constraints-holdp (seq-ij-elem-gadget ty wires)
                                                asg (base-prime)))
             (and (not (reserrp (seq-ij-out ty wires asg)))
                  (not (equal (seq-ij-out ty wires asg) :error)))))

  (defthm seq-ij-elem-complete
    (implies (and (seq-ij-wiresp ty wires)
                  (not (reserrp (inject-impl mode v)))
                  (member-equal mode '(:public :private))
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (seq-shared-ok asg)
                  (seq-agree wires asg (seq-ij-elem-witness ty wires v)))
             (and (r1cs::r1cs-constraints-holdp (seq-ij-elem-gadget ty wires)
                                                asg (base-prime))
                  (equal (seq-ij-out ty wires asg)
                         (inject-impl mode v))))))

(defun seq-ij-elem-spec (ty mode v)
  (declare (ignore ty))
  (inject-impl mode v))

(defun seq-ij-seq-spec (tys mode vs)
  (declare (ignore tys))
  (inject-seq-funspec mode (true-list-fix vs)))

(seq-instantiate-inject
 seq-ij
 :wiresp seq-ij-wiresp :gadget seq-ij-elem-gadget :out seq-ij-out
 :spec seq-ij-elem-spec :witness seq-ij-elem-witness :spec-seq seq-ij-seq-spec
 :theory (enable seq-ij-elem-spec seq-ij-seq-spec inject-seq-funspec
                 true-list-fix
                 seq-ij-blocks-wiresp seq-ij-gadget seq-ij-outs seq-ij-witness
                 seq-ij-blocks-disjointp))

(defruled seq-ij-container-sound
  (implies (and (seq-ij-blocks-wiresp blocks)
                (member-equal mode '(:public :private))
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg (seq-blocks-wires blocks))
                (seq-shared-ok asg)
                (r1cs::r1cs-constraints-holdp (seq-ij-gadget blocks)
                                              asg (base-prime)))
           (equal (inject-seq-funspec mode (seq-ij-outs blocks asg))
                  (seq-ij-outs blocks asg)))
  :use ((:instance seq-ij-gadget-sound))
  :prep-lemmas
  ((defrule true-listp-of-seq-ij-outs
     (true-listp (seq-ij-outs blocks asg)))))

(defruled seq-ij-container-complete
  (implies (and (seq-ij-blocks-wiresp blocks)
                (seq-ij-blocks-disjointp blocks)
                (member-equal mode '(:public :private))
                (true-listp vs)
                (equal (len vs) (len blocks))
                (not (reserrp (inject-seq-funspec mode vs))))
           (b* ((asg (seq-ij-witness blocks vs)))
             (and (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-binds-allp asg (seq-blocks-wires blocks))
                  (seq-shared-ok asg)
                  (r1cs::r1cs-constraints-holdp (seq-ij-gadget blocks)
                                                asg (base-prime))
                  (equal (seq-ij-outs blocks asg)
                         (inject-seq-funspec mode vs)))))
  :use ((:instance seq-ij-gadget-complete))
  :disable (seq-ij-gadget-complete seq-ij-witness seq-ij-outs seq-ij-gadget
                                   seq-ij-blocks-wiresp seq-blocks-wires
                                   inject-seq-funspec))
