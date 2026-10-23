; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parametric soundness and completeness of snarkVM's sequencing
; combinators (circuit/environment/src/traits/{to_bits,inject}.rs):
; Vec<C>, [C; N], &[C] and tuples write the bits of each element in
; order into one vector, and Inject::new for Vec and tuples injects each
; component.  They add no constraint of their own; the container circuit
; is the concatenation of the element circuits, each element owning its
; own fresh wires.
;
; Interface (stable; reused by the seq-, ptx- and rec- books).
;
; A container is described by a list of BLOCKS, one per element, each
; block a pair (TY . WIRES): TY is an element type tag (ignored by
; homogeneous instances such as Vec<Field>; it distinguishes the
; components of a heterogeneous tuple) and WIRES are the wires the
; element circuit allocates.  The constant-one variable and any other
; wire shared by all elements is in (SEQ-SHARED-WIRES).
;
; Element interface for write_bits (constrained functions):
;   (seq-elem-wiresp ty wires)      well-formed wire block
;   (seq-elem-valp ty x)            element type predicate
;   (seq-elem-gadget ty wires)      element constraints
;   (seq-elem-in ty wires asg)      element value read from the wires
;   (seq-elem-out ty wires asg)     element bits read from the wires
;   (seq-elem-spec ty acc x)        element write_bits funspec
;   (seq-elem-witness ty wires x)   witness alist for WIRES on input X
;   (seq-shared-wires) (seq-shared-witness) (seq-shared-ok asg)
; with constraints
;   seq-elem-sound:    a satisfying assignment gives an input of the
;                      element type whose funspec appends the output bits;
;   seq-elem-complete: any valuation agreeing with the witness on WIRES
;                      (and with the shared witness on the shared wires)
;                      satisfies the element constraints, with input X.
; Completeness only constrains the gadget on the element's own wires and
; the shared wires; that and pairwise disjointness of blocks is what makes
; the per-element witnesses combine (seq-witness).
;
; Element interface for Inject::new: seq-inj-* below, same shape, with
; the element funspec (seq-inj-spec ty mode v) returning the injected
; value or an error.
;
; Container theorems:
;   seq-gadget-sound, seq-gadget-complete            (write_bits)
;   seq-inj-gadget-sound, seq-inj-gadget-complete    (Inject::new)
; Instantiate with :functional-instance; see seq-instances.lisp.

(in-package "ALEOVM")

(include-book "../fun-specs/primitives-environment")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(local (include-book "kestrel/alists-light/lookup-equal" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/alists/top" :dir :system))

(local (in-theory (disable base-prime (:e base-prime))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Agreement of two valuations on a list of wires.

(defun seq-agree (ws a b)
  (declare (xargs :guard (and (true-listp ws) (alistp a) (alistp b))))
  (if (endp ws)
      t
    (and (equal (lookup-equal (car ws) a) (lookup-equal (car ws) b))
         (seq-agree (cdr ws) a b))))

(defrule seq-assoc-equal-iff-member-strip-cars
  (implies (alistp a)
           (iff (assoc-equal k a)
                (member-equal k (strip-cars a)))))

(defruled seq-intersectp-commute
  (iff (intersectp-equal a b)
       (intersectp-equal b a))
  :prep-lemmas
  ((defrule seq-intersectp-of-cons-right
     (iff (intersectp-equal a (cons x b))
          (or (member-equal x a)
              (intersectp-equal a b)))
     :induct (len a)))
  :induct (len a))

(defrule seq-agree-refl
  (seq-agree ws a a))

(defruled seq-agree-of-append-skip-0
  (implies (and (alistp a)
                (not (intersectp-equal ws (strip-cars a)))
                (seq-agree ws b c))
           (seq-agree ws (append a b) c))
  :induct (seq-agree ws b c)
  :enable acl2::lookup-equal-of-append)

(defruled seq-agree-of-append-skip
  (implies (and (alistp a)
                (not (intersectp-equal (strip-cars a) ws))
                (seq-agree ws b c))
           (seq-agree ws (append a b) c))
  :use (seq-agree-of-append-skip-0
        (:instance seq-intersectp-commute (a (strip-cars a)) (b ws))))

(defruled seq-agree-of-append-hit
  (implies (and (alistp a)
                (subsetp-equal ws (strip-cars a)))
           (seq-agree ws (append a b) a))
  :induct (len ws)
  :enable acl2::lookup-equal-of-append)

(defruled seq-agree-of-append-hit-2
  (implies (and (alistp a)
                (subsetp-equal ws (strip-cars a))
                (seq-agree ws a c))
           (seq-agree ws (append a b) c))
  :induct (len ws)
  :enable acl2::lookup-equal-of-append)

(defruled seq-binds-all-when-subsetp
  (implies (subsetp-equal ws (strip-cars a))
           (r1cs::valuation-binds-allp a ws))
  :induct (len ws)
  :enable (r1cs::valuation-binds-allp r1cs::valuation-bindsp))

(defrule seq-no-dups-of-append
  (equal (no-duplicatesp-equal (append a b))
         (and (no-duplicatesp-equal a)
              (no-duplicatesp-equal b)
              (not (intersectp-equal a b))))
  :induct (len a))

(defrule seq-intersectp-of-append-left
  (equal (intersectp-equal (append a b) c)
         (or (intersectp-equal a c)
             (intersectp-equal b c)))
  :induct (len a))

(defrule seq-intersectp-of-append-right
  (equal (intersectp-equal a (append b c))
         (or (intersectp-equal a b)
             (intersectp-equal a c)))
  :induct (len a))

(defruled seq-r1cs-valuationp-of-append
  (implies (and (r1cs::r1cs-valuationp a p)
                (r1cs::r1cs-valuationp b p)
                (not (intersectp-equal (strip-cars a) (strip-cars b))))
           (r1cs::r1cs-valuationp (append a b) p))
  :enable r1cs::r1cs-valuationp
  :prep-lemmas
  ((defrule seq-no-dups-of-append
     (equal (no-duplicatesp-equal (append a b))
            (and (no-duplicatesp-equal a)
                 (no-duplicatesp-equal b)
                 (not (intersectp-equal a b))))
     :induct (len a))
   (defrule seq-symbol-listp-of-append
     (implies (and (symbol-listp a) (symbol-listp b))
              (symbol-listp (append a b))))
   (defrule seq-fe-listp-of-append
     (implies (and (pfield::fe-listp a p) (pfield::fe-listp b p))
              (pfield::fe-listp (append a b) p))
     :enable pfield::fe-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Shared wires (the constant-one variable and the like).

(encapsulate
  (((seq-shared-wires) => *)
   ((seq-shared-witness) => *)
   ((seq-shared-ok *) => *))

  (local (defun seq-shared-wires () nil))
  (local (defun seq-shared-witness () nil))
  (local (defun seq-shared-ok (asg) (declare (ignore asg)) t))

  (defthm seq-shared-wires-props
    (and (symbol-listp (seq-shared-wires))
         (no-duplicatesp-equal (seq-shared-wires))
         (r1cs::r1cs-valuationp (seq-shared-witness) (base-prime))
         (alistp (seq-shared-witness))
         (equal (strip-cars (seq-shared-witness)) (seq-shared-wires))))

  (defthm seq-shared-ok-when-agree
    (implies (seq-agree (seq-shared-wires) asg (seq-shared-witness))
             (seq-shared-ok asg))))

;; Element interface (write_bits).

(encapsulate
  (((seq-elem-wiresp * *) => *)
   ((seq-elem-valp * *) => *)
   ((seq-elem-gadget * *) => *)
   ((seq-elem-in * * *) => *)
   ((seq-elem-out * * *) => *)
   ((seq-elem-spec * * *) => *)
   ((seq-elem-witness * * *) => *))

  (local (defun seq-elem-wiresp (ty wires)
           (declare (ignore ty))
           (null wires)))
  (local (defun seq-elem-valp (ty x) (declare (ignore ty)) (equal x 0)))
  (local (defun seq-elem-gadget (ty wires) (declare (ignore ty wires)) nil))
  (local (defun seq-elem-in (ty wires asg) (declare (ignore ty wires asg)) 0))
  (local (defun seq-elem-out (ty wires asg) (declare (ignore ty wires asg)) nil))
  (local (defun seq-elem-spec (ty acc x) (declare (ignore ty x)) (append acc nil)))
  (local (defun seq-elem-witness (ty wires x)
           (declare (ignore ty wires x))
           nil))

  (defthm seq-elem-wiresp-necc
    (implies (seq-elem-wiresp ty wires)
             (and (symbol-listp wires)
                  (no-duplicatesp-equal wires))))

  (defthm true-listp-of-seq-elem-out
    (true-listp (seq-elem-out ty wires asg)))

  (defthm seq-elem-witness-props
    (implies (and (seq-elem-wiresp ty wires)
                  (seq-elem-valp ty x))
             (and (r1cs::r1cs-valuationp (seq-elem-witness ty wires x)
                                         (base-prime))
                  (equal (strip-cars (seq-elem-witness ty wires x)) wires))))

  (defthm alistp-of-seq-elem-witness
    (implies (and (seq-elem-wiresp ty wires)
                  (seq-elem-valp ty x))
             (alistp (seq-elem-witness ty wires x))))

  (defthm seq-elem-sound
    (implies (and (seq-elem-wiresp ty wires)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-binds-allp asg wires)
                  (seq-shared-ok asg)
                  (r1cs::r1cs-constraints-holdp (seq-elem-gadget ty wires)
                                                asg (base-prime)))
             (and (seq-elem-valp ty (seq-elem-in ty wires asg))
                  (equal (seq-elem-spec ty acc (seq-elem-in ty wires asg))
                         (append acc (seq-elem-out ty wires asg))))))

  (defthm seq-elem-complete
    (implies (and (seq-elem-wiresp ty wires)
                  (seq-elem-valp ty x)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (seq-shared-ok asg)
                  (seq-agree wires asg (seq-elem-witness ty wires x)))
             (and (r1cs::r1cs-constraints-holdp (seq-elem-gadget ty wires)
                                                asg (base-prime))
                  (equal (seq-elem-in ty wires asg) x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Blocks: well-formedness and disjointness.

(defun seq-blocks-wires (blocks)
  (declare (xargs :guard t))
  (if (atom blocks)
      nil
    (append (and (consp (car blocks)) (true-list-fix (cdar blocks)))
            (seq-blocks-wires (cdr blocks)))))

(defun seq-blocks-tys (blocks)
  (declare (xargs :guard t))
  (if (atom blocks)
      nil
    (cons (and (consp (car blocks)) (caar blocks))
          (seq-blocks-tys (cdr blocks)))))

(defun seq-blocks-wiresp (blocks)
  (if (atom blocks)
      (null blocks)
    (and (consp (car blocks))
         (true-listp (cdar blocks))
         (seq-elem-wiresp (caar blocks) (cdar blocks))
         (seq-blocks-wiresp (cdr blocks)))))

(defun seq-blocks-disjointp (blocks)
  (no-duplicatesp-equal (append (seq-blocks-wires blocks)
                                (seq-shared-wires))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The container circuit (write_bits on Vec, [C; N], &[C], tuples).

(defun seq-gadget (blocks)
  (if (atom blocks)
      nil
    (append (seq-elem-gadget (caar blocks) (cdar blocks))
            (seq-gadget (cdr blocks)))))

(defun seq-ins (blocks asg)
  (if (atom blocks)
      nil
    (cons (seq-elem-in (caar blocks) (cdar blocks) asg)
          (seq-ins (cdr blocks) asg))))

(defun seq-outs (blocks asg)
  (if (atom blocks)
      nil
    (append (seq-elem-out (caar blocks) (cdar blocks) asg)
            (seq-outs (cdr blocks) asg))))

(defun seq-valsp (tys xs)
  (if (atom tys)
      (null xs)
    (and (consp xs)
         (seq-elem-valp (car tys) (car xs))
         (seq-valsp (cdr tys) (cdr xs)))))

(defun seq-spec (tys acc xs)
  (if (atom xs)
      acc
    (seq-spec (cdr tys) (seq-elem-spec (car tys) acc (car xs)) (cdr xs))))

(defun seq-witness (blocks xs)
  (if (atom blocks)
      (seq-shared-witness)
    (append (seq-elem-witness (caar blocks) (cdar blocks) (car xs))
            (seq-witness (cdr blocks) (cdr xs)))))

(defun seq-agree-blocks (blocks xs asg)
  (if (atom blocks)
      t
    (and (seq-agree (cdar blocks) asg
                    (seq-elem-witness (caar blocks) (cdar blocks) (car xs)))
         (seq-agree-blocks (cdr blocks) (cdr xs) asg))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Soundness.

(local (in-theory (disable (:e seq-witness) (:e seq-blocks-disjointp)
                           (:e seq-gadget) (:e seq-ins) (:e seq-outs)
                           (:e seq-spec) (:e seq-valsp) (:e seq-agree-blocks)
                           (:e seq-blocks-wiresp))))

(defrule seq-gadget-sound
  (implies (and (seq-blocks-wiresp blocks)
                (true-listp acc)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg (seq-blocks-wires blocks))
                (seq-shared-ok asg)
                (r1cs::r1cs-constraints-holdp (seq-gadget blocks)
                                              asg (base-prime)))
           (and (seq-valsp (seq-blocks-tys blocks) (seq-ins blocks asg))
                (equal (seq-spec (seq-blocks-tys blocks) acc
                                 (seq-ins blocks asg))
                       (append acc (seq-outs blocks asg)))))
  :induct (seq-spec-ind blocks acc asg)
  :prep-lemmas
  ((defun seq-spec-ind (blocks acc asg)
     (if (atom blocks)
         (list acc asg)
       (seq-spec-ind (cdr blocks)
                     (append acc (seq-elem-out (caar blocks) (cdar blocks) asg))
                     asg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Completeness.

(defruled seq-gadget-complete-agree
  (implies (and (seq-blocks-wiresp blocks)
                (seq-valsp (seq-blocks-tys blocks) xs)
                (r1cs::r1cs-valuationp asg (base-prime))
                (seq-shared-ok asg)
                (seq-agree-blocks blocks xs asg))
           (and (r1cs::r1cs-constraints-holdp (seq-gadget blocks)
                                              asg (base-prime))
                (equal (seq-ins blocks asg) xs)))
  :induct (seq-witness blocks xs))

(defrule seq-strip-cars-of-seq-witness
  (implies (and (seq-blocks-wiresp blocks)
                (seq-valsp (seq-blocks-tys blocks) xs))
           (equal (strip-cars (seq-witness blocks xs))
                  (append (seq-blocks-wires blocks) (seq-shared-wires)))))

(defrule seq-witness-valuationp
  (implies (and (seq-blocks-wiresp blocks)
                (seq-valsp (seq-blocks-tys blocks) xs)
                (no-duplicatesp-equal (append (seq-blocks-wires blocks)
                                              (seq-shared-wires))))
           (r1cs::r1cs-valuationp (seq-witness blocks xs) (base-prime)))
  :induct (seq-witness blocks xs)
  :enable seq-r1cs-valuationp-of-append)

(defruled seq-witness-agree-shared
  (implies (and (seq-blocks-wiresp blocks)
                (seq-valsp (seq-blocks-tys blocks) xs)
                (no-duplicatesp-equal (append (seq-blocks-wires blocks)
                                              (seq-shared-wires))))
           (seq-agree (seq-shared-wires) (seq-witness blocks xs)
                      (seq-shared-witness)))
  :induct (seq-witness blocks xs)
  :enable seq-agree-of-append-skip)

(defruled seq-agree-of-append-skip-blocks
  (implies (and (alistp a)
                (not (intersectp-equal (strip-cars a) (seq-blocks-wires blocks)))
                (seq-agree-blocks blocks xs b))
           (seq-agree-blocks blocks xs (append a b)))
  :induct (seq-agree-blocks blocks xs b)
  :enable seq-agree-of-append-skip)

(defruled seq-witness-agree-blocks
  (implies (and (seq-blocks-wiresp blocks)
                (seq-valsp (seq-blocks-tys blocks) xs)
                (no-duplicatesp-equal (append (seq-blocks-wires blocks)
                                              (seq-shared-wires))))
           (seq-agree-blocks blocks xs (seq-witness blocks xs)))
  :induct (seq-witness blocks xs)
  :enable (seq-agree-of-append-hit seq-agree-of-append-skip-blocks))

(defrule seq-gadget-complete
  (implies (and (seq-blocks-wiresp blocks)
                (true-listp acc)
                (seq-blocks-disjointp blocks)
                (seq-valsp (seq-blocks-tys blocks) xs))
           (b* ((asg (seq-witness blocks xs)))
             (and (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-binds-allp asg (seq-blocks-wires blocks))
                  (seq-shared-ok asg)
                  (r1cs::r1cs-constraints-holdp (seq-gadget blocks)
                                                asg (base-prime))
                  (equal (seq-ins blocks asg) xs)
                  (equal (append acc (seq-outs blocks asg))
                         (seq-spec (seq-blocks-tys blocks) acc xs)))))
  :do-not-induct t
  :use ((:instance seq-gadget-complete-agree (asg (seq-witness blocks xs)))
        (:instance seq-witness-agree-blocks)
        (:instance seq-witness-agree-shared)
        (:instance seq-gadget-sound (asg (seq-witness blocks xs)))
        (:instance seq-binds-all-when-subsetp
                   (ws (seq-blocks-wires blocks))
                   (a (seq-witness blocks xs))))
  :disable (seq-gadget-sound seq-witness seq-ins seq-outs seq-spec
                             seq-gadget seq-blocks-wires)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Element interface (Inject::new).  Variable modes only: snarkVM folds
;; constants at synthesis time.

(encapsulate
  (((seq-inj-wiresp * *) => *)
   ((seq-inj-gadget * *) => *)
   ((seq-inj-out * * *) => *)
   ((seq-inj-spec * * *) => *)
   ((seq-inj-witness * * *) => *))

  (local (defun seq-inj-wiresp (ty wires)
           (declare (ignore ty))
           (null wires)))
  (local (defun seq-inj-gadget (ty wires) (declare (ignore ty wires)) nil))
  (local (defun seq-inj-out (ty wires asg) (declare (ignore ty wires asg)) 0))
  (local (defun seq-inj-spec (ty mode v) (declare (ignore ty mode v)) 0))
  (local (defun seq-inj-witness (ty wires v)
           (declare (ignore ty wires v))
           nil))


  (defthm seq-inj-wiresp-necc
    (implies (seq-inj-wiresp ty wires)
             (and (symbol-listp wires)
                  (no-duplicatesp-equal wires))))

  (defthm seq-inj-witness-props
    (implies (and (seq-inj-wiresp ty wires)
                  (member-equal mode '(:public :private))
                  (not (reserrp (seq-inj-spec ty mode v))))
             (and (r1cs::r1cs-valuationp (seq-inj-witness ty wires v)
                                         (base-prime))
                  (equal (strip-cars (seq-inj-witness ty wires v)) wires))))

  (defthm alistp-of-seq-inj-witness
    (implies (and (seq-inj-wiresp ty wires)
                  (member-equal mode '(:public :private))
                  (not (reserrp (seq-inj-spec ty mode v))))
             (alistp (seq-inj-witness ty wires v))))

  (defthm seq-inj-sound
    (implies (and (seq-inj-wiresp ty wires)
                  (member-equal mode '(:public :private))
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-binds-allp asg wires)
                  (seq-shared-ok asg)
                  (r1cs::r1cs-constraints-holdp (seq-inj-gadget ty wires)
                                                asg (base-prime)))
             (equal (seq-inj-spec ty mode (seq-inj-out ty wires asg))
                    (seq-inj-out ty wires asg))))

  (defthm seq-inj-sound-not-error
    (implies (and (seq-inj-wiresp ty wires)
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-binds-allp asg wires)
                  (seq-shared-ok asg)
                  (r1cs::r1cs-constraints-holdp (seq-inj-gadget ty wires)
                                                asg (base-prime)))
             (and (not (reserrp (seq-inj-out ty wires asg)))
                  (not (equal (seq-inj-out ty wires asg) :error)))))

  (defthm seq-inj-complete
    (implies (and (seq-inj-wiresp ty wires)
                  (member-equal mode '(:public :private))
                  (not (reserrp (seq-inj-spec ty mode v)))
                  (r1cs::r1cs-valuationp asg (base-prime))
                  (seq-shared-ok asg)
                  (seq-agree wires asg (seq-inj-witness ty wires v)))
             (and (r1cs::r1cs-constraints-holdp (seq-inj-gadget ty wires)
                                                asg (base-prime))
                  (equal (seq-inj-out ty wires asg)
                         (seq-inj-spec ty mode v))))))

(defun seq-inj-blocks-wiresp (blocks)
  (if (atom blocks)
      (null blocks)
    (and (consp (car blocks))
         (true-listp (cdar blocks))
         (seq-inj-wiresp (caar blocks) (cdar blocks))
         (seq-inj-blocks-wiresp (cdr blocks)))))

(defun seq-inj-gadget-list (blocks)
  (if (atom blocks)
      nil
    (append (seq-inj-gadget (caar blocks) (cdar blocks))
            (seq-inj-gadget-list (cdr blocks)))))

(defun seq-inj-outs (blocks asg)
  (if (atom blocks)
      nil
    (cons (seq-inj-out (caar blocks) (cdar blocks) asg)
          (seq-inj-outs (cdr blocks) asg))))

(defun seq-inj-seq-spec (tys mode vs)
  (declare (xargs :measure (len vs)))
  (b* (((when (atom vs)) nil)
       (first (seq-inj-spec (car tys) mode (car vs)))
       ((when (reserrp first)) (spec-error))
       (rest (seq-inj-seq-spec (cdr tys) mode (cdr vs)))
       ((when (reserrp rest)) (spec-error)))
    (cons first rest)))

(defun seq-inj-witness-list (blocks vs)
  (if (atom blocks)
      (seq-shared-witness)
    (append (seq-inj-witness (caar blocks) (cdar blocks) (car vs))
            (seq-inj-witness-list (cdr blocks) (cdr vs)))))

(defun seq-inj-agree-blocks (blocks vs asg)
  (if (atom blocks)
      t
    (and (seq-agree (cdar blocks) asg
                    (seq-inj-witness (caar blocks) (cdar blocks) (car vs)))
         (seq-inj-agree-blocks (cdr blocks) (cdr vs) asg))))

(defun seq-inj-oksp (tys mode vs)
  (declare (xargs :measure (len vs)))
  (if (atom vs)
      t
    (and (not (reserrp (seq-inj-spec (car tys) mode (car vs))))
         (seq-inj-oksp (cdr tys) mode (cdr vs)))))

(local (in-theory (disable (:e seq-inj-witness-list) (:e seq-inj-gadget-list)
                           (:e seq-inj-outs) (:e seq-inj-seq-spec)
                           (:e seq-inj-agree-blocks) (:e seq-inj-oksp)
                           (:e seq-inj-blocks-wiresp))))

(defrule seq-not-reserrp-of-cons
  (implies (not (equal a :error))
           (not (reserrp (cons a b))))
  :enable reserrp)

(defrule seq-inj-oksp-when-not-error
  (implies (not (reserrp (seq-inj-seq-spec tys mode vs)))
           (seq-inj-oksp tys mode vs))
  :induct (seq-inj-oksp tys mode vs))

(defrule seq-inj-outs-oksp
  (implies (and (seq-inj-blocks-wiresp blocks)
                (member-equal mode '(:public :private))
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg (seq-blocks-wires blocks))
                (seq-shared-ok asg)
                (r1cs::r1cs-constraints-holdp (seq-inj-gadget-list blocks)
                                              asg (base-prime)))
           (seq-inj-oksp (seq-blocks-tys blocks) mode (seq-inj-outs blocks asg)))
  :induct (seq-inj-outs blocks asg)
  :hints (("Subgoal *1/2"
           :use ((:instance seq-inj-sound (ty (caar blocks)) (wires (cdar blocks)))
                 (:instance seq-inj-sound-not-error (ty (caar blocks))
                            (wires (cdar blocks)))))))

(defrule seq-inj-outs-not-reserrp
  (implies (and (seq-inj-blocks-wiresp blocks)
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg (seq-blocks-wires blocks))
                (seq-shared-ok asg)
                (r1cs::r1cs-constraints-holdp (seq-inj-gadget-list blocks)
                                              asg (base-prime)))
           (not (reserrp (seq-inj-outs blocks asg))))
  :induct (seq-inj-outs blocks asg))

(defrule seq-inj-gadget-sound
  (implies (and (seq-inj-blocks-wiresp blocks)
                (member-equal mode '(:public :private))
                (r1cs::r1cs-valuationp asg (base-prime))
                (r1cs::valuation-binds-allp asg (seq-blocks-wires blocks))
                (seq-shared-ok asg)
                (r1cs::r1cs-constraints-holdp (seq-inj-gadget-list blocks)
                                              asg (base-prime)))
           (equal (seq-inj-seq-spec (seq-blocks-tys blocks) mode
                                    (seq-inj-outs blocks asg))
                  (seq-inj-outs blocks asg)))
  :induct (seq-inj-outs blocks asg)
  :hints (("Subgoal *1/2"
           :use ((:instance seq-inj-sound (ty (caar blocks)) (wires (cdar blocks)))
                 (:instance seq-inj-sound-not-error (ty (caar blocks))
                            (wires (cdar blocks)))))))

(defruled seq-inj-gadget-complete-agree
  (implies (and (seq-inj-blocks-wiresp blocks)
                (member-equal mode '(:public :private))
                (equal (len vs) (len blocks))
                (not (reserrp (seq-inj-seq-spec (seq-blocks-tys blocks) mode vs)))
                (r1cs::r1cs-valuationp asg (base-prime))
                (seq-shared-ok asg)
                (seq-inj-agree-blocks blocks vs asg))
           (and (r1cs::r1cs-constraints-holdp (seq-inj-gadget-list blocks)
                                              asg (base-prime))
                (equal (seq-inj-outs blocks asg)
                       (seq-inj-seq-spec (seq-blocks-tys blocks) mode vs))))
  :induct (seq-inj-witness-list blocks vs)
  :hints (("Subgoal *1/2"
           :use ((:instance seq-inj-complete (ty (caar blocks))
                            (wires (cdar blocks)) (v (car vs)))))))

(defrule seq-strip-cars-of-seq-inj-witness-list
  (implies (and (seq-inj-blocks-wiresp blocks)
                (member-equal mode '(:public :private))
                (equal (len vs) (len blocks))
                (seq-inj-oksp (seq-blocks-tys blocks) mode vs))
           (equal (strip-cars (seq-inj-witness-list blocks vs))
                  (append (seq-blocks-wires blocks) (seq-shared-wires))))
  :induct (seq-inj-witness-list blocks vs)
  :hints (("Subgoal *1/2" :use ((:instance seq-inj-witness-props
                                           (ty (caar blocks))
                                           (wires (cdar blocks))
                                           (v (car vs)))))))

(defruled seq-inj-witness-list-valuationp
  (implies (and (seq-inj-blocks-wiresp blocks)
                (member-equal mode '(:public :private))
                (equal (len vs) (len blocks))
                (seq-inj-oksp (seq-blocks-tys blocks) mode vs)
                (no-duplicatesp-equal (append (seq-blocks-wires blocks)
                                              (seq-shared-wires))))
           (r1cs::r1cs-valuationp (seq-inj-witness-list blocks vs) (base-prime)))
  :induct (seq-inj-witness-list blocks vs)
  :enable seq-r1cs-valuationp-of-append
  :hints (("Subgoal *1/2" :use ((:instance seq-inj-witness-props
                                           (ty (caar blocks))
                                           (wires (cdar blocks))
                                           (v (car vs)))
                                (:instance seq-strip-cars-of-seq-inj-witness-list
                                           (blocks (cdr blocks))
                                           (vs (cdr vs)))))))

(defruled seq-inj-witness-agree-shared
  (implies (and (seq-inj-blocks-wiresp blocks)
                (member-equal mode '(:public :private))
                (equal (len vs) (len blocks))
                (seq-inj-oksp (seq-blocks-tys blocks) mode vs)
                (no-duplicatesp-equal (append (seq-blocks-wires blocks)
                                              (seq-shared-wires))))
           (seq-agree (seq-shared-wires) (seq-inj-witness-list blocks vs)
                      (seq-shared-witness)))
  :induct (seq-inj-witness-list blocks vs)
  :enable seq-agree-of-append-skip
  :hints (("Subgoal *1/2" :use ((:instance seq-inj-witness-props
                            (ty (caar blocks))
                            (wires (cdar blocks))
                            (v (car vs)))))))

(defruled seq-agree-of-append-skip-inj-blocks
  (implies (and (alistp a)
                (not (intersectp-equal (strip-cars a) (seq-blocks-wires blocks)))
                (seq-inj-agree-blocks blocks vs b))
           (seq-inj-agree-blocks blocks vs (append a b)))
  :induct (seq-inj-agree-blocks blocks vs b)
  :enable seq-agree-of-append-skip)

(defruled seq-inj-witness-agree-blocks
  (implies (and (seq-inj-blocks-wiresp blocks)
                (member-equal mode '(:public :private))
                (equal (len vs) (len blocks))
                (seq-inj-oksp (seq-blocks-tys blocks) mode vs)
                (no-duplicatesp-equal (append (seq-blocks-wires blocks)
                                              (seq-shared-wires))))
           (seq-inj-agree-blocks blocks vs (seq-inj-witness-list blocks vs)))
  :induct (seq-inj-witness-list blocks vs)
  :enable (seq-agree-of-append-hit seq-agree-of-append-skip-inj-blocks)
  :hints (("Subgoal *1/2" :use ((:instance seq-inj-witness-props
                                           (ty (caar blocks))
                                           (wires (cdar blocks))
                                           (v (car vs)))
                                (:instance seq-strip-cars-of-seq-inj-witness-list
                                           (blocks (cdr blocks))
                                           (vs (cdr vs)))))))

(defrule seq-inj-gadget-complete
  (implies (and (seq-inj-blocks-wiresp blocks)
                (seq-blocks-disjointp blocks)
                (member-equal mode '(:public :private))
                (equal (len vs) (len blocks))
                (not (reserrp (seq-inj-seq-spec (seq-blocks-tys blocks) mode vs))))
           (b* ((asg (seq-inj-witness-list blocks vs)))
             (and (r1cs::r1cs-valuationp asg (base-prime))
                  (r1cs::valuation-binds-allp asg (seq-blocks-wires blocks))
                  (seq-shared-ok asg)
                  (r1cs::r1cs-constraints-holdp (seq-inj-gadget-list blocks)
                                                asg (base-prime))
                  (equal (seq-inj-outs blocks asg)
                         (seq-inj-seq-spec (seq-blocks-tys blocks) mode vs)))))
  :do-not-induct t
  :use ((:instance seq-inj-gadget-complete-agree
                   (asg (seq-inj-witness-list blocks vs)))
        (:instance seq-inj-witness-list-valuationp)
        (:instance seq-inj-witness-agree-blocks)
        (:instance seq-inj-witness-agree-shared)
        (:instance seq-strip-cars-of-seq-inj-witness-list)
        (:instance seq-inj-oksp-when-not-error (tys (seq-blocks-tys blocks)))
        (:instance seq-binds-all-when-subsetp
                   (ws (seq-blocks-wires blocks))
                   (a (seq-inj-witness-list blocks vs))))
  :disable (seq-inj-witness-list seq-inj-outs seq-inj-seq-spec
                                 seq-inj-gadget-list seq-blocks-wires
)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Instantiation macros.
;;
;; (seq-instantiate-write-bits NAME :wiresp f :valp f :gadget f :in f :out f
;;                             :spec f :witness f
;;                             [:shared-wires f :shared-witness f :shared-ok f]
;;                             [:spec-seq f] [:theory th] [:hints h])
;; defines NAME-blocks-wiresp, NAME-gadget, NAME-ins, NAME-outs, NAME-valsp,
;; NAME-spec (unless :spec-seq names an existing function equal to the
;; accumulator fold of :spec), NAME-witness, NAME-blocks-disjointp, and
;; proves NAME-gadget-sound and NAME-gadget-complete by functional
;; instantiation of seq-gadget-sound and seq-gadget-complete.  All the
;; f are function symbols with the arities of the seq-elem-* functions.
;; :theory (an in-theory expression for "Goal") and :hints are used for
;; the constraint obligations.
;;
;; (seq-instantiate-inject NAME :wiresp f :gadget f :out f :spec f :witness f
;;                         [:shared-wires f :shared-witness f :shared-ok f]
;;                         [:spec-seq f] [:theory th] [:hints h])
;; does the same for seq-inj-gadget-sound and seq-inj-gadget-complete.

(defun seq-mk-name (name suffix)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name name) suffix) name))

(defun seq-nonidentity-pairs (alist)
  (declare (xargs :mode :program))
  (cond ((endp alist) nil)
        ((eq (caar alist) (cdar alist)) (seq-nonidentity-pairs (cdr alist)))
        (t (cons (list (caar alist) (cdar alist))
                 (seq-nonidentity-pairs (cdr alist))))))

(defun seq-instantiate-thm-fn (thm-name base-thm alist theory hints state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((f (acl2::formula base-thm nil (w state)))
         (pairs (seq-nonidentity-pairs alist)))
    `(defthm ,thm-name
       ,(sublis alist f)
       :hints (("Goal" :use ((:functional-instance ,base-thm ,@pairs))
                ,@(and theory `(:in-theory ,theory)))
               ,@hints))))

(defmacro seq-instantiate-write-bits (name &key wiresp valp gadget in out spec
                                           witness
                                           (shared-wires 'seq-shared-wires)
                                           (shared-witness 'seq-shared-witness)
                                           (shared-ok 'seq-shared-ok)
                                           spec-seq theory hints)
  (let* ((bw (seq-mk-name name "-BLOCKS-WIRESP"))
         (gd (seq-mk-name name "-GADGET"))
         (ins (seq-mk-name name "-INS"))
         (outs (seq-mk-name name "-OUTS"))
         (vals (seq-mk-name name "-VALSP"))
         (sp (or spec-seq (seq-mk-name name "-SPEC")))
         (wit (seq-mk-name name "-WITNESS"))
         (dj (seq-mk-name name "-BLOCKS-DISJOINTP"))
         (alist `((seq-elem-wiresp . ,wiresp) (seq-elem-valp . ,valp)
                  (seq-elem-gadget . ,gadget) (seq-elem-in . ,in)
                  (seq-elem-out . ,out) (seq-elem-spec . ,spec)
                  (seq-elem-witness . ,witness)
                  (seq-shared-wires . ,shared-wires)
                  (seq-shared-witness . ,shared-witness)
                  (seq-shared-ok . ,shared-ok)
                  (seq-blocks-wiresp . ,bw) (seq-gadget . ,gd)
                  (seq-ins . ,ins) (seq-outs . ,outs) (seq-valsp . ,vals)
                  (seq-spec . ,sp) (seq-witness . ,wit)
                  (seq-blocks-disjointp . ,dj))))
    `(progn
       (defun ,bw (blocks)
         (if (atom blocks)
             (null blocks)
           (and (consp (car blocks))
                (true-listp (cdar blocks))
                (,wiresp (caar blocks) (cdar blocks))
                (,bw (cdr blocks)))))
       (defun ,gd (blocks)
         (if (atom blocks)
             nil
           (append (,gadget (caar blocks) (cdar blocks))
                   (,gd (cdr blocks)))))
       (defun ,ins (blocks asg)
         (if (atom blocks)
             nil
           (cons (,in (caar blocks) (cdar blocks) asg)
                 (,ins (cdr blocks) asg))))
       (defun ,outs (blocks asg)
         (if (atom blocks)
             nil
           (append (,out (caar blocks) (cdar blocks) asg)
                   (,outs (cdr blocks) asg))))
       (defun ,vals (tys xs)
         (if (atom tys)
             (null xs)
           (and (consp xs)
                (,valp (car tys) (car xs))
                (,vals (cdr tys) (cdr xs)))))
       ,@(and (not spec-seq)
              `((defun ,sp (tys acc xs)
                  (if (atom xs)
                      acc
                    (,sp (cdr tys) (,spec (car tys) acc (car xs)) (cdr xs))))))
       (defun ,wit (blocks xs)
         (if (atom blocks)
             (,shared-witness)
           (append (,witness (caar blocks) (cdar blocks) (car xs))
                   (,wit (cdr blocks) (cdr xs)))))
       (defun ,dj (blocks)
         (no-duplicatesp-equal (append (seq-blocks-wires blocks)
                                       (,shared-wires))))
       (make-event (seq-instantiate-thm-fn ',(seq-mk-name name "-GADGET-SOUND")
                                           'seq-gadget-sound ',alist ',theory
                                           ',hints state))
       (make-event (seq-instantiate-thm-fn ',(seq-mk-name name "-GADGET-COMPLETE")
                                           'seq-gadget-complete ',alist ',theory
                                           ',hints state)))))

(defmacro seq-instantiate-inject (name &key wiresp gadget out spec witness
                                       (shared-wires 'seq-shared-wires)
                                       (shared-witness 'seq-shared-witness)
                                       (shared-ok 'seq-shared-ok)
                                       spec-seq theory hints)
  (let* ((bw (seq-mk-name name "-BLOCKS-WIRESP"))
         (gd (seq-mk-name name "-GADGET"))
         (outs (seq-mk-name name "-OUTS"))
         (sp (or spec-seq (seq-mk-name name "-SEQ-SPEC")))
         (wit (seq-mk-name name "-WITNESS"))
         (dj (seq-mk-name name "-BLOCKS-DISJOINTP"))
         (alist `((seq-inj-wiresp . ,wiresp) (seq-inj-gadget . ,gadget)
                  (seq-inj-out . ,out) (seq-inj-spec . ,spec)
                  (seq-inj-witness . ,witness)
                  (seq-shared-wires . ,shared-wires)
                  (seq-shared-witness . ,shared-witness)
                  (seq-shared-ok . ,shared-ok)
                  (seq-inj-blocks-wiresp . ,bw) (seq-inj-gadget-list . ,gd)
                  (seq-inj-outs . ,outs) (seq-inj-seq-spec . ,sp)
                  (seq-inj-witness-list . ,wit)
                  (seq-blocks-disjointp . ,dj))))
    `(progn
       (defun ,bw (blocks)
         (if (atom blocks)
             (null blocks)
           (and (consp (car blocks))
                (true-listp (cdar blocks))
                (,wiresp (caar blocks) (cdar blocks))
                (,bw (cdr blocks)))))
       (defun ,gd (blocks)
         (if (atom blocks)
             nil
           (append (,gadget (caar blocks) (cdar blocks))
                   (,gd (cdr blocks)))))
       (defun ,outs (blocks asg)
         (if (atom blocks)
             nil
           (cons (,out (caar blocks) (cdar blocks) asg)
                 (,outs (cdr blocks) asg))))
       ,@(and (not spec-seq)
              `((defun ,sp (tys mode vs)
                  (declare (xargs :measure (len vs)))
                  (b* (((when (atom vs)) nil)
                       (first (,spec (car tys) mode (car vs)))
                       ((when (reserrp first)) (spec-error))
                       (rest (,sp (cdr tys) mode (cdr vs)))
                       ((when (reserrp rest)) (spec-error)))
                    (cons first rest)))))
       (defun ,wit (blocks vs)
         (if (atom blocks)
             (,shared-witness)
           (append (,witness (caar blocks) (cdar blocks) (car vs))
                   (,wit (cdr blocks) (cdr vs)))))
       (defun ,dj (blocks)
         (no-duplicatesp-equal (append (seq-blocks-wires blocks)
                                       (,shared-wires))))
       (make-event (seq-instantiate-thm-fn ',(seq-mk-name name "-GADGET-SOUND")
                                           'seq-inj-gadget-sound ',alist ',theory
                                           ',hints state))
       (make-event (seq-instantiate-thm-fn ',(seq-mk-name name "-GADGET-COMPLETE")
                                           'seq-inj-gadget-complete ',alist ',theory
                                           ',hints state)))))
