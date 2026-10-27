; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The BHP wrappers of snarkVM circuit/network/src/v0.rs:
;
;   commit_bhpN(input, r)          = BHP_N.commit(input, r)
;   commit_to_group_bhpN(input, r) = BHP_N.commit_uncompressed(input, r)
;   hash_to_group_bhpN(input)      = BHP_N.hash_uncompressed(input)
;
; The BHP_N instances are constants, so each wrapper emits exactly the
; constraints of the certified algorithm gadget at size N (hbhp-cu-gadget,
; hbhp-hu-gadget).  Each theorem below instantiates the algorithm theorem at
; the size and rewrites its specification to the Aleo funspec.

(in-package "ALEOVM")

(include-book "hbhp-cu")
(include-book "../fun-specs/curve-network")

(defruled net-bhp-commit-is-funspec
  (equal (curve-commit-bhp size bits r)
         (hbhp-bhp-commit size bits r))
  :enable (curve-commit-bhp bhp-commit-uncompressed hbhp-bhp-commit))

(defruled net-bhp-commit-to-group-is-funspec
  (equal (bhp-commit-uncompressed size bits r)
         (hbhp-bhp-commit-uncompressed size bits r))
  :enable bhp-commit-uncompressed)

(defruled net-bhp-hash-to-group-is-funspec
  (equal (bhp-hash-uncompressed size bits)
         (hbhp-bhp-hash-uncompressed size bits))
  :enable bhp-hash-uncompressed)

(defmacro net-bhp-hyps (n)
  `(and (equal size ,n)
        (equal p (base-prime))
        (r1cs::r1cs-valuationp asg p)
        (equal w (hbhp-size-window-size size))
        (equal gens (hbhp-setup-gens size))
        (equal domain (hbhp-size-domain size))
        (equal rgen (hbhp-setup-random-base size))
        (equal m (floor 84 w))
        (equal c (mod 84 w))
        (equal cbits (append (hbhp-domain-bits domain)
                             (acl2::nat=>lebits 64 (mod (len vb) (expt 2 64)))))
        (equal max (hbhp-max-bits-per-iteration gens w))
        (symbolp u) (r1cs::valuation-bindsp asg u) (equal (lookup-equal u asg) 1)))

(defun net-sym (pre s n post)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol
   (concatenate 'string pre s (coerce (explode-nonnegative-integer n 10 nil) 'string) post)
   'net-sym))

(defmacro net-bhp-instance (n)
  (flet ((name (s n) (net-sym "NET-" s n ""))
         (fn (s n) (net-sym "ALEO-" s n "-FUNSPEC")))
    `(progn
       (defruled ,(name "COMMIT-BHP-SOUND-" n)
         (implies (and (net-bhp-hyps ,n)
                       (hbhp-cu-wires-okp cbits vb wins0 its gens w m c max s rbits rs sts asg)
                       (r1cs::r1cs-constraints-holdp
                        (hbhp-cu-gadget cbits vb wins0 its gens w m c max u s rbits rs sts rgen p)
                        asg p))
                  (b* ((out (hbhp-cu-out cbits vb wins0 its gens w m c max rbits sts)))
                    (and (fieldp (nfix (hbhp-lk (car out))))
                         (equal (nfix (hbhp-lk (car out)))
                                (,(fn "COMMIT-BHP" n) (hbhp-lk-list vb asg)
                                 (lookup-equal s asg))))))
         :use (hbhp-bhp-commit-sound
               (:instance net-bhp-commit-is-funspec
                          (bits (hbhp-lk-list vb asg)) (r (lookup-equal s asg)))
               (:instance fieldp-of-curve-commit-bhp
                          (bits (hbhp-lk-list vb asg)) (randomizer (lookup-equal s asg))))
         :in-theory '(,(fn "COMMIT-BHP" n) (:e member-equal)))

       (defruled ,(name "COMMIT-BHP-COMPLETE-" n)
         (implies (and (net-bhp-hyps ,n)
                       (hbhp-cu-wires-okp cbits vb wins0 its gens w m c max s rbits rs sts asg)
                       (hbhp-cu-canon cbits vb wins0 its gens w m c max s rbits rs sts rgen asg))
                  (r1cs::r1cs-constraints-holdp
                   (hbhp-cu-gadget cbits vb wins0 its gens w m c max u s rbits rs sts rgen p)
                   asg p))
         :use hbhp-bhp-cu-complete
         :in-theory '((:e member-equal)))

       (defruled ,(name "COMMIT-TO-GROUP-BHP-SOUND-" n)
         (implies (and (net-bhp-hyps ,n)
                       (hbhp-cu-wires-okp cbits vb wins0 its gens w m c max s rbits rs sts asg)
                       (r1cs::r1cs-constraints-holdp
                        (hbhp-cu-gadget cbits vb wins0 its gens w m c max u s rbits rs sts rgen p)
                        asg p))
                  (b* ((out (hbhp-cu-out cbits vb wins0 its gens w m c max rbits sts))
                       (pt (ecurve::point-finite (hbhp-lk (car out)) (hbhp-lk (cdr out)))))
                    (and (groupp pt)
                         (equal pt
                                (,(fn "COMMIT-TO-GROUP-BHP" n) (hbhp-lk-list vb asg)
                                 (lookup-equal s asg))))))
         :use (hbhp-bhp-cu-sound
               (:instance net-bhp-commit-to-group-is-funspec
                          (bits (hbhp-lk-list vb asg)) (r (lookup-equal s asg)))
               (:instance groupp-of-bhp-commit-uncompressed
                          (input-bits (hbhp-lk-list vb asg))
                          (randomizer (lookup-equal s asg))))
         :in-theory '(,(fn "COMMIT-TO-GROUP-BHP" n) (:e member-equal)))

       (defruled ,(name "COMMIT-TO-GROUP-BHP-COMPLETE-" n)
         (implies (and (net-bhp-hyps ,n)
                       (hbhp-cu-wires-okp cbits vb wins0 its gens w m c max s rbits rs sts asg)
                       (hbhp-cu-canon cbits vb wins0 its gens w m c max s rbits rs sts rgen asg))
                  (r1cs::r1cs-constraints-holdp
                   (hbhp-cu-gadget cbits vb wins0 its gens w m c max u s rbits rs sts rgen p)
                   asg p))
         :use hbhp-bhp-cu-complete
         :in-theory '((:e member-equal)))

       (defruled ,(name "HASH-TO-GROUP-BHP-SOUND-" n)
         (implies (and (net-bhp-hyps ,n)
                       (hbhp-hu-wires-okp cbits vb wins0 its gens w m c max asg)
                       (consp vb)
                       (r1cs::r1cs-constraints-holdp
                        (hbhp-hu-gadget cbits vb wins0 its gens w m c max u p) asg p))
                  (b* ((out (hbhp-hu-out cbits vb wins0 its gens w m c max))
                       (pt (ecurve::point-finite (lookup-equal (car out) asg)
                                                 (lookup-equal (cdr out) asg))))
                    (and (groupp pt)
                         (equal pt (,(fn "HASH-TO-GROUP-BHP" n) (hbhp-lk-list vb asg))))))
         :use (hbhp-bhp-hu-sound
               (:instance net-bhp-hash-to-group-is-funspec (bits (hbhp-lk-list vb asg)))
               (:instance groupp-of-bhp-hash-uncompressed
                          (input-bits (hbhp-lk-list vb asg))))
         :in-theory '(,(fn "HASH-TO-GROUP-BHP" n) (:e member-equal)))

       (defruled ,(name "HASH-TO-GROUP-BHP-EMPTY-" n)
         (implies (and (equal size ,n)
                       (equal w (hbhp-size-window-size size))
                       (equal gens (hbhp-setup-gens size))
                       (equal domain (hbhp-size-domain size))
                       (not (consp vb)))
                  (and (equal (hbhp-hu-gadget cbits vb wins0 its gens w m c max u p) nil)
                       (equal (,(fn "HASH-TO-GROUP-BHP" n) (hbhp-lk-list vb asg))
                              (ecurve::twisted-edwards-zero))))
         :use (hbhp-bhp-hu-empty
               (:instance net-bhp-hash-to-group-is-funspec (bits (hbhp-lk-list vb asg))))
         :in-theory '(,(fn "HASH-TO-GROUP-BHP" n) (:e member-equal)))

       (defruled ,(name "HASH-TO-GROUP-BHP-COMPLETE-" n)
         (implies (and (net-bhp-hyps ,n)
                       (hbhp-hu-wires-okp cbits vb wins0 its gens w m c max asg)
                       (consp vb)
                       (hbhp-hu-canon cbits vb wins0 its gens w m c max asg))
                  (r1cs::r1cs-constraints-holdp
                   (hbhp-hu-gadget cbits vb wins0 its gens w m c max u p) asg p))
         :use hbhp-bhp-hu-complete
         :in-theory '((:e member-equal))))))

(net-bhp-instance 256)
(net-bhp-instance 512)
(net-bhp-instance 768)
(net-bhp-instance 1024)
