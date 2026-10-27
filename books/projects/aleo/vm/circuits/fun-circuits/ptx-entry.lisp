; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Entry<Plaintext> circuits (snarkVM circuit/program/src/data/record/entry),
; composed from the Plaintext circuits of ptx-tree, ptx-bits, ptx-new and
; ptx-equal.
;
; An entry wire is (mode . wt) with mode one of :constant, :public,
; :private (a synthesis-time tag) and wt a plaintext wire tree.  The
; visibility bits of write_bits_le / write_bits_be / to_fields are
; Boolean::constant, so they are constant terms.
;
; write_bits_le_with_visibility_as_mode with Mode::Constant is
; write_bits_le.  With Mode::Public / Mode::Private snarkVM allocates the
; two visibility bits with Boolean::new, which only constrains them to be
; booleans; nothing ties them to the entry's visibility, so that circuit is
; not sound for the funspec and is not modelled here.

(in-package "ALEOVM")

(include-book "ptx-bits")
(include-book "ptx-new")
(include-book "ptx-equal")

(set-verify-guards-eagerness 0)

(define ptx-ewtp (ew)
  (and (consp ew)
       (member-equal (car ew) '(:constant :public :private))
       (ptx-wtp (cdr ew))))

(define ptx-entry-wrap (mode pt)
  (case mode
    (:constant (entry-constant pt))
    (:public (entry-public pt))
    (otherwise (entry-private pt))))

(define ptx-eval (ew asg)
  :short "Eject: the entry an entry wire denotes."
  (ptx-entry-wrap (car ew) (ptx-val (cdr ew) asg)))

(define ptx-vis-bits (mode)
  (case mode
    (:constant (list 0 0))
    (:public (list 0 1))
    (otherwise (list 1 0))))

(defruled ptx-entry-plaintext-of-wrap
  (implies (plaintextp pt)
           (equal (values-entry-plaintext (ptx-entry-wrap mode pt)) pt))
  :enable (ptx-entry-wrap values-entry-plaintext))

(defruled ptx-entry-vis-bits-of-wrap
  (equal (values-entry-visibility-bits (ptx-entry-wrap mode pt))
         (ptx-vis-bits mode))
  :enable (ptx-entry-wrap values-entry-visibility-bits ptx-vis-bits))

(local (in-theory (enable ptx-entry-plaintext-of-wrap
                          ptx-entry-vis-bits-of-wrap
                          ptx-eval)))

(defruled ptx-entry-new-of-wrap
  (implies (plaintextp pt)
           (equal (entry-new (ptx-entry-wrap mode pt))
                  (if (reserrp (plaintext-new pt))
                      (plaintext-new pt)
                    (ptx-entry-wrap mode (plaintext-new pt)))))
  :enable (entry-new ptx-entry-wrap values-entry-plaintext))

(defruled ptx-entry-find-of-wrap
  (implies (plaintextp pt)
           (equal (entry-find (ptx-entry-wrap mode pt) path)
                  (if (reserrp (plaintext-find pt path))
                      (plaintext-find pt path)
                    (ptx-entry-wrap mode (plaintext-find pt path)))))
  :enable (entry-find ptx-entry-wrap values-entry-plaintext))

(defrule ptx-not-reserrp-of-wrap
  (not (reserrp (ptx-entry-wrap mode pt)))
  :enable ptx-entry-wrap)

(defrule ptx-entryp-of-eval
  (entryp (ptx-eval ew asg))
  :enable ptx-entry-wrap)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Entry::new: Plaintext::new on the data, the mode is the tag.

(define ptx-entry-new-gadget (ew)
  (ptx-new-gadget (cdr ew)))

(defruled ptx-entry-new-sound
  (implies (and (primep p)
                (ptx-ewtp ew)
                (ptx-distinct (ptx-val (cdr ew) asg))
                (r1cs::r1cs-constraints-holdp (ptx-entry-new-gadget ew) asg p))
           (and (ptx-typed (cdr ew) asg)
                (equal (entry-new (ptx-eval ew asg))
                       (ptx-eval ew asg))))
  :use ((:instance ptx-new-sound (wt (cdr ew))))
  :enable (ptx-ewtp ptx-entry-new-gadget ptx-entry-new-of-wrap))

(defruled ptx-entry-new-complete
  (implies (and (primep p)
                (ptx-ewtp ew)
                (plaintextp pt)
                (ptx-distinct pt)
                (ptx-new-witnessp (cdr ew) pt asg p))
           (if (reserrp (plaintext-new pt))
               (not (r1cs::r1cs-constraints-holdp (ptx-entry-new-gadget ew) asg p))
             (and (r1cs::r1cs-constraints-holdp (ptx-entry-new-gadget ew) asg p)
                  (equal (ptx-eval ew asg)
                         (entry-new (ptx-entry-wrap (car ew) pt))))))
  :use ((:instance ptx-new-complete (wt (cdr ew))))
  :enable (ptx-ewtp ptx-entry-new-gadget ptx-entry-new-of-wrap))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Entry::find: the constant-path walk of Plaintext::find; no constraints.

(define ptx-entry-find (ew path)
  (b* ((out (ptx-find (cdr ew) path)))
    (if (equal out :error) :error (cons (car ew) out))))

(define ptx-entry-find-gadget ()
  nil)

(defruled ptx-entry-find-sound
  (implies (and (ptx-ewtp ew)
                (r1cs::r1cs-constraints-holdp (ptx-entry-find-gadget) asg p))
           (b* ((out (ptx-entry-find ew path))
                (spec (entry-find (ptx-eval ew asg) path)))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (and (ptx-ewtp out)
                                (equal (ptx-eval out asg) spec))))))
  :use ((:instance ptx-find-sound (wt (cdr ew)) (p p)))
  :enable (ptx-ewtp ptx-entry-find ptx-entry-find-of-wrap ptx-find-gadget
                    ptx-entry-find-gadget))

(defruled ptx-entry-find-complete
  (r1cs::r1cs-constraints-holdp (ptx-entry-find-gadget) asg p)
  :enable ptx-entry-find-gadget)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Entry::is_equal / is_not_equal: a mode mismatch is the constant false
;; (true); otherwise Plaintext::is_equal / is_not_equal.

(define ptx-entry-eq (ea eb neq names)
  (if (equal (car ea) (car eb))
      (ptx-eq (cdr ea) (cdr eb) neq names)
    (cons nil (if neq 1 0))))

(define ptx-entry-eq-witnessp (ea eb neq names asg p)
  (or (not (equal (car ea) (car eb)))
      (ptx-eq-witnessp (cdr ea) (cdr eb) neq names asg p)))

(defruled ptx-entry-kind-of-wrap
  (implies (ptx-ewtp ew)
           (equal (entry-kind (ptx-entry-wrap (car ew) pt))
                  (car ew)))
  :enable (ptx-ewtp ptx-entry-wrap))

(defruled ptx-entry-eq-sound
  (implies (and (primep p)
                (symbol-listp names)
                (ptx-ewtp ea)
                (ptx-ewtp eb)
                (ptx-typed (cdr ea) asg)
                (ptx-typed (cdr eb) asg)
                (r1cs::r1cs-constraints-holdp (car (ptx-entry-eq ea eb neq names))
                                              asg p))
           (equal (ptx-bval (cdr (ptx-entry-eq ea eb neq names)) asg p)
                  (if neq
                      (entry-is-not-equal (ptx-eval ea asg) (ptx-eval eb asg))
                    (entry-is-equal (ptx-eval ea asg) (ptx-eval eb asg)))))
  :use ((:instance ptx-eq-sound (a (cdr ea)) (b (cdr eb)))
        (:instance ptx-entry-kind-of-wrap (ew ea) (pt (ptx-val (cdr ea) asg)))
        (:instance ptx-entry-kind-of-wrap (ew eb) (pt (ptx-val (cdr eb) asg))))
  :enable (ptx-entry-eq entry-is-equal entry-is-not-equal values-entry-equalp
                        values-bool-to-bit))

(defruled ptx-entry-eq-complete
  (implies (and (primep p)
                (r1cs::r1cs-valuationp asg p)
                (symbol-listp names)
                (ptx-typed (cdr ea) asg)
                (ptx-typed (cdr eb) asg)
                (ptx-entry-eq-witnessp ea eb neq names asg p))
           (r1cs::r1cs-constraints-holdp (car (ptx-entry-eq ea eb neq names))
                                         asg p))
  :use ((:instance ptx-eq-complete (a (cdr ea)) (b (cdr eb))))
  :enable (ptx-entry-eq ptx-entry-eq-witnessp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Entry::write_bits_le (= write_bits_le_with_visibility_as_mode with
;; Mode::Constant) and Entry::write_bits_be: the constant visibility bits
;; followed by Plaintext::write_bits_le / _be.

(define ptx-entry-bits-out (ew bigp)
  (append (ptx-vis-bits (car ew)) (ptx-bits-out (cdr ew) bigp)))

(define ptx-entry-bits-gadget (ew bigp)
  (ptx-bits-gadget (cdr ew) bigp))

(defrule ptx-terms-val-of-vis-bits
  (equal (ptx-terms-val (ptx-vis-bits mode) asg)
         (ptx-vis-bits mode))
  :enable (ptx-vis-bits ptx-terms-val-of-cons))

(defruled ptx-entry-write-bits-le-sound
  (implies (and (primep p)
                (ptx-ewtp ew)
                (ptx-typed (cdr ew) asg)
                (r1cs::r1cs-constraints-holdp (ptx-entry-bits-gadget ew nil) asg p))
           (and (equal (ptx-terms-val (ptx-entry-bits-out ew nil) asg)
                       (entry-to-bits-le (ptx-eval ew asg)))
                (equal (ptx-terms-val (ptx-entry-bits-out ew nil) asg)
                       (entry-write-bits-le-with-visibility-as-mode
                        (ptx-eval ew asg)))))
  :use ((:instance ptx-write-bits-le-sound (wt (cdr ew))))
  :enable (ptx-ewtp ptx-entry-bits-out ptx-entry-bits-gadget entry-to-bits-le
                    entry-write-bits-le-with-visibility-as-mode))

(defruled ptx-entry-write-bits-be-sound
  (implies (and (primep p)
                (ptx-ewtp ew)
                (ptx-typed (cdr ew) asg)
                (r1cs::r1cs-constraints-holdp (ptx-entry-bits-gadget ew t) asg p))
           (equal (ptx-terms-val (ptx-entry-bits-out ew t) asg)
                  (entry-to-bits-be (ptx-eval ew asg))))
  :use ((:instance ptx-write-bits-be-sound (wt (cdr ew))))
  :enable (ptx-ewtp ptx-entry-bits-out ptx-entry-bits-gadget entry-to-bits-be))

(defruled ptx-entry-write-bits-complete
  (implies (and (primep p)
                (ptx-ewtp ew)
                (ptx-typed (cdr ew) asg)
                (ptx-bits-witnessp (cdr ew) bigp asg p))
           (r1cs::r1cs-constraints-holdp (ptx-entry-bits-gadget ew bigp) asg p))
  :use ((:instance ptx-write-bits-complete (wt (cdr ew))))
  :enable (ptx-ewtp ptx-entry-bits-gadget))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Entry::to_fields (= to_fields_with_visibility_as_mode with
;; Mode::Constant): write_bits_le, a constant 1, packed with
;; Field::from_bits_le per chunk (linear, no constraints).

(define ptx-entry-to-fields-out (ew)
  (ptx-to-fields-out (append (ptx-entry-bits-out ew nil) (list 1))))

(defruled ptx-entry-to-fields-sound
  (implies (and (primep p)
                (ptx-ewtp ew)
                (ptx-typed (cdr ew) asg)
                (r1cs::r1cs-constraints-holdp (ptx-entry-bits-gadget ew nil) asg p))
           (b* ((out (ptx-entry-to-fields-out ew))
                (spec (entry-to-fields (ptx-eval ew asg))))
             (and (equal spec
                         (entry-to-fields-with-visibility-as-mode
                          (ptx-eval ew asg)))
                  (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal (ptx-chunks-val out asg) spec)))))
  :use ((:instance ptx-to-fields-out-correct
         (terms (append (ptx-entry-bits-out ew nil) (list 1))))
        ptx-entry-write-bits-le-sound)
  :enable (ptx-entry-to-fields-out entry-to-fields
                                   entry-to-fields-with-visibility-as-mode))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Entry::num_randomizers: a synthesis-time constant.

(define ptx-entry-num-randomizers (ew)
  (if (equal (car ew) :private) (ptx-size-in-fields (cdr ew)) 0))

(defruled ptx-entry-num-randomizers-sound
  (implies (and (primep p)
                (ptx-ewtp ew)
                (ptx-typed (cdr ew) asg)
                (r1cs::r1cs-constraints-holdp (ptx-entry-bits-gadget ew nil) asg p))
           (b* ((out (ptx-entry-num-randomizers ew))
                (spec (entry-num-randomizers (ptx-eval ew asg))))
             (and (iff (equal out :error) (reserrp spec))
                  (implies (not (equal out :error))
                           (equal out spec)))))
  :use ((:instance ptx-size-in-fields-sound (wt (cdr ew))))
  :enable (ptx-ewtp ptx-entry-num-randomizers entry-num-randomizers
                    ptx-entry-wrap ptx-entry-bits-gadget))
