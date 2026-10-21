; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The Pedersen wrappers of snarkVM circuit/network/src/v0.rs:
;
;   commit_pedN(input, r)          = PEDERSEN_N.commit(input, r)
;   commit_to_group_pedN(input, r) = PEDERSEN_N.commit_uncompressed(input, r)
;   hash_to_group_pedN(input)      = PEDERSEN_N.hash_uncompressed(input)
;
; The PEDERSEN_N instances are constants with bases (hped-setup-bases N) and
; random bases (hped-setup-random-bases N), so each wrapper emits exactly the
; certified gadget of hped-pedersen.lisp at those bases.  Inputs longer than
; N halt in snarkVM (and are excluded by the gadget hypothesis
; len bits <= len bases); the funspecs return an error there.

(in-package "ALEOVM")

(include-book "hped-pedersen")
(include-book "../fun-specs/curve-network")

(defruledl net-ped-not-reserrp-when-r-pointp
  (implies (ecurve::edwards-bls12-r-pointp x)
           (not (reserrp x)))
  :use ((:instance ecurve::edwards-bls12-pointp-when-edwards-bls12-r-pointp (ecurve::x x))
        (:instance curve-not-reserrp-when-pointp))
  :in-theory '(ecurve::edwards-bls12-pointp))

(defruled net-ped-hash-r-pointp
  (implies (<= (len bits) (nfix size))
           (ecurve::edwards-bls12-r-pointp
            (hped-pedersen-hash-uncompressed size (hped-setup-bases size) bits)))
  :enable hped-pedersen-hash-uncompressed
  :use ((:instance hped-ped-r-pointp-of-sum
                   (bits (hped-ped-pad bits size)) (bases (hped-setup-bases size))
                   (acc (ecurve::twisted-edwards-zero)))))

(defruled net-ped-commit-r-pointp
  (implies (<= (len bits) (nfix size))
           (ecurve::edwards-bls12-r-pointp
            (hped-pedersen-commit-uncompressed size (hped-setup-bases size)
                                               (hped-setup-random-bases size) bits r)))
  :enable (hped-pedersen-commit-uncompressed net-ped-not-reserrp-when-r-pointp)
  :use (net-ped-hash-r-pointp
        (:instance hped-ped-r-pointp-of-sum
                   (bits (hped-ped-randomizer-bits r)) (bases (hped-setup-random-bases size))
                   (acc (hped-pedersen-hash-uncompressed size (hped-setup-bases size) bits)))))

(defruled net-ped-hash-to-group-is-funspec
  (implies (and (natp size) (<= (len bits) size))
           (equal (curve-hash-to-group-ped size bits)
                  (hped-pedersen-hash-uncompressed size (hped-setup-bases size) bits)))
  :enable (curve-hash-to-group-ped pedersen-hash-uncompressed
           hped-aleo-pedersen-hash-uncompressed hped-pedersen-hash-uncompressed-total
           hped-pedersen-hash-uncompressed net-ped-not-reserrp-when-r-pointp)
  :use ((:instance hped-ped-r-pointp-of-sum
                   (bits (hped-ped-pad bits size)) (bases (hped-setup-bases size))
                   (acc (ecurve::twisted-edwards-zero)))))

(defruled net-ped-commit-to-group-is-funspec
  (implies (and (natp size) (<= (len bits) size))
           (equal (curve-commit-to-group-ped size bits r)
                  (hped-pedersen-commit-uncompressed size (hped-setup-bases size)
                                                     (hped-setup-random-bases size)
                                                     bits r)))
  :enable (curve-commit-to-group-ped pedersen-commit-uncompressed
           hped-aleo-pedersen-commit-uncompressed hped-pedersen-commit-uncompressed-total
           hped-pedersen-commit-uncompressed hped-pedersen-hash-uncompressed
           net-ped-not-reserrp-when-r-pointp)
  :use ((:instance hped-ped-r-pointp-of-sum
                   (bits (hped-ped-pad bits size)) (bases (hped-setup-bases size))
                   (acc (ecurve::twisted-edwards-zero)))
        (:instance hped-ped-r-pointp-of-sum
                   (bits (hped-ped-randomizer-bits r)) (bases (hped-setup-random-bases size))
                   (acc (hped-ped-sum (hped-ped-pad bits size) (hped-setup-bases size)
                                      (ecurve::twisted-edwards-zero))))))

(defruled net-ped-commit-is-funspec
  (implies (and (natp size) (<= (len bits) size))
           (equal (curve-commit-ped size bits r)
                  (hped-pedersen-commit size (hped-setup-bases size)
                                        (hped-setup-random-bases size)
                                        bits r)))
  :enable (curve-commit-ped hped-pedersen-commit net-ped-commit-to-group-is-funspec))

(defun net-ped-sym (pre s n post)
  (declare (xargs :mode :program))
  (intern-in-package-of-symbol
   (concatenate 'string pre s (coerce (explode-nonnegative-integer n 10 nil) 'string) post)
   'net-ped-sym))

(defruled net-ped-commit-fieldp
  (implies (<= (len bits) (nfix size))
           (fieldp (hped-pedersen-commit size (hped-setup-bases size)
                                         (hped-setup-random-bases size) bits r)))
  :use (net-ped-commit-r-pointp
        (:instance curve-x-of-groupp-is-fieldp
                   (p (hped-pedersen-commit-uncompressed size (hped-setup-bases size)
                                                         (hped-setup-random-bases size)
                                                         bits r))))
  :in-theory '(hped-pedersen-commit groupp net-ped-not-reserrp-when-r-pointp))

(defmacro net-ped-instance (n)
  (flet ((name (s n) (net-ped-sym "NET-" s n ""))
         (fn (s n) (net-ped-sym "ALEO-" s n "-FUNSPEC")))
    `(progn
       (defruled ,(name "HASH-TO-GROUP-PED-SOUND-" n)
         (implies (and (equal num-bits ,n)
                       (equal bases (hped-setup-bases ,n))
                       (hped-ped-zero-hyps)
                       (r1cs::r1cs-constraints-holdp (hped-ped-from-zero-gadget bits bases wss)
                                                     asg (base-prime)))
                  (b* ((out (hped-ped-from-zero-out bits bases wss))
                       (pt (ecurve::point-finite (r1cs::dot-product (car out) asg (base-prime))
                                                 (r1cs::dot-product (cdr out) asg (base-prime)))))
                    (and (groupp pt)
                         (equal pt (,(fn "HASH-TO-GROUP-PED" n) (lookup-equal-list bits asg))))))
         :use (hped-pedersen-hash-uncompressed-gadget-sound
               (:instance net-ped-hash-to-group-is-funspec
                          (size ,n) (bits (lookup-equal-list bits asg)))
               (:instance return-type-of-curve-hash-to-group-ped
                          (size ,n) (bits (lookup-equal-list bits asg)))
               (:instance net-ped-hash-r-pointp
                          (size ,n) (bits (lookup-equal-list bits asg))))
         :in-theory '(,(fn "HASH-TO-GROUP-PED" n) hped-len-of-setup-bases
                      hped-ped-r-pointp-of-hash-uncompressed
                      hped-ped-r-point-listp-of-setup-bases len-of-lookup-equal-list
                      groupp (:e nfix) (:e natp)))

       (defruled ,(name "HASH-TO-GROUP-PED-COMPLETE-" n)
         (implies (and (equal num-bits ,n)
                       (equal bases (hped-setup-bases ,n))
                       (hped-ped-zero-hyps)
                       (hped-ped-from-zero-canonp bits bases wss asg))
                  (r1cs::r1cs-constraints-holdp (hped-ped-from-zero-gadget bits bases wss)
                                                asg (base-prime)))
         :use hped-pedersen-hash-uncompressed-gadget-complete
         :in-theory '(hped-len-of-setup-bases (:e nfix)))

       (defruled ,(name "COMMIT-TO-GROUP-PED-SOUND-" n)
         (implies (and (equal num-bits ,n)
                       (equal bases (hped-setup-bases ,n))
                       (equal rbases (hped-setup-random-bases ,n))
                       (hped-ped-commit-hyps)
                       (r1cs::r1cs-constraints-holdp
                        (hped-ped-commit-gadget bits bases wss s xs rs rbases rwss)
                        asg (base-prime)))
                  (b* ((out (hped-ped-commit-out bits bases wss xs rbases rwss))
                       (pt (ecurve::point-finite (r1cs::dot-product (car out) asg (base-prime))
                                                 (r1cs::dot-product (cdr out) asg (base-prime)))))
                    (and (scalarp (lookup-equal s asg))
                         (groupp pt)
                         (equal pt (,(fn "COMMIT-TO-GROUP-PED" n)
                                    (lookup-equal-list bits asg) (lookup-equal s asg))))))
         :use (hped-pedersen-commit-uncompressed-gadget-sound
               (:instance net-ped-commit-to-group-is-funspec
                          (size ,n) (bits (lookup-equal-list bits asg)) (r (lookup-equal s asg)))
               (:instance return-type-of-curve-commit-to-group-ped
                          (size ,n) (bits (lookup-equal-list bits asg))
                          (randomizer (lookup-equal s asg)))
               (:instance net-ped-commit-r-pointp
                          (size ,n) (bits (lookup-equal-list bits asg))
                          (r (lookup-equal s asg))))
         :in-theory '(,(fn "COMMIT-TO-GROUP-PED" n) hped-len-of-setup-bases
                      hped-ped-r-pointp-of-commit-uncompressed
                      hped-ped-r-point-listp-of-setup-bases
                      hped-ped-r-point-listp-of-setup-random-bases
                      len-of-lookup-equal-list groupp (:e nfix) (:e natp)))

       (defruled ,(name "COMMIT-TO-GROUP-PED-COMPLETE-" n)
         (implies (and (equal num-bits ,n)
                       (equal bases (hped-setup-bases ,n))
                       (equal rbases (hped-setup-random-bases ,n))
                       (hped-ped-commit-hyps)
                       (hped-ped-commit-canonp bits bases wss s xs rs rbases rwss asg))
                  (r1cs::r1cs-constraints-holdp
                   (hped-ped-commit-gadget bits bases wss s xs rs rbases rwss)
                   asg (base-prime)))
         :use hped-pedersen-commit-uncompressed-gadget-complete
         :in-theory '(hped-len-of-setup-bases (:e nfix)))

       (defruled ,(name "COMMIT-PED-SOUND-" n)
         (implies (and (equal num-bits ,n)
                       (equal bases (hped-setup-bases ,n))
                       (equal rbases (hped-setup-random-bases ,n))
                       (hped-ped-commit-hyps)
                       (r1cs::r1cs-constraints-holdp
                        (hped-ped-commit-gadget bits bases wss s xs rs rbases rwss)
                        asg (base-prime)))
                  (b* ((out (hped-ped-commit-out bits bases wss xs rbases rwss))
                       (x (r1cs::dot-product (car out) asg (base-prime))))
                    (and (fieldp x)
                         (equal x (,(fn "COMMIT-PED" n)
                                   (lookup-equal-list bits asg) (lookup-equal s asg))))))
         :use (hped-pedersen-commit-gadget-sound
               (:instance net-ped-commit-is-funspec
                          (size ,n) (bits (lookup-equal-list bits asg)) (r (lookup-equal s asg)))
               (:instance net-ped-commit-fieldp
                          (size ,n) (bits (lookup-equal-list bits asg)) (r (lookup-equal s asg))))
         :in-theory '(,(fn "COMMIT-PED" n) hped-len-of-setup-bases
                      len-of-lookup-equal-list (:e nfix) (:e natp)))

       (defruled ,(name "COMMIT-PED-COMPLETE-" n)
         (implies (and (equal num-bits ,n)
                       (equal bases (hped-setup-bases ,n))
                       (equal rbases (hped-setup-random-bases ,n))
                       (hped-ped-commit-hyps)
                       (hped-ped-commit-canonp bits bases wss s xs rs rbases rwss asg))
                  (r1cs::r1cs-constraints-holdp
                   (hped-ped-commit-gadget bits bases wss s xs rs rbases rwss)
                   asg (base-prime)))
         :use hped-pedersen-commit-gadget-complete
         :in-theory '(hped-len-of-setup-bases (:e nfix))))))

(net-ped-instance 64)
(net-ped-instance 128)
