; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Aleo::verify_merkle_path_bhp / _psd (circuit/network/src/v0.rs) are
; MerklePath::verify with (BHP1024, BHP512) and (Poseidon4, Poseidon2).
; The network funspecs aleo-verify-merkle-path-{bhp,psd}-funspec
; (curve-network.lisp) agree with crypto-merkle-path-verify
; (crypto-merkle.lisp) at hashers (:bhp . 1024)/(:bhp . 512) and
; (:poseidon . 4)/(:poseidon . 2), which is the specification of the
; MerklePath::verify circuit theorems.

(in-package "ALEOVM")

(include-book "../fun-specs/crypto-merkle")

(local (include-book "std/lists/top" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/utilities/bits-as-digits" :dir :system))

(defruled net-mrk-crypto-hash-bhp
  (equal (crypto-hash-bhp size bits)
         (ecurve::point-finite->x (bhp-hash-uncompressed size bits)))
  :use (:instance groupp-of-bhp-hash-uncompressed (input-bits bits))
  :enable (crypto-hash-bhp crypto-group-x groupp ecurve::edwards-bls12-point->u))

(defruled net-mrk-field-bits
  (implies (fieldp x)
           (equal (crypto-field-bits-le x) (curve-field-to-bits-le x)))
  :enable (crypto-field-bits-le crypto-nat->lebits curve-field-to-bits-le
           fieldp pfield::fep base-field-size-in-bits)
  :prep-lemmas
  ((defruled net-mrk-base-prime-bound
     (< (base-prime) (expt 2 253))
     :in-theory '((:e base-prime) (:e expt) (:e <)))))

(defruled net-mrk-leaf-bhp
  (equal (crypto-merkle-hash-leaf '(:bhp . 1024) leaf)
         (curve-merkle-hash-leaf-bhp leaf))
  :enable (crypto-merkle-hash-leaf curve-merkle-hash-leaf-bhp net-mrk-crypto-hash-bhp))

(defruled net-mrk-children-bhp
  (implies (and (fieldp l) (fieldp r))
           (equal (crypto-merkle-hash-children '(:bhp . 512) (list l r))
                  (curve-merkle-hash-children-bhp l r)))
  :enable (crypto-merkle-hash-children curve-merkle-hash-children-bhp
           net-mrk-crypto-hash-bhp crypto-merkle-hash-list-bits
           crypto-merkle-hash-bits crypto-keccak-hasher-p net-mrk-field-bits))

(defruled net-mrk-leaf-psd
  (equal (crypto-merkle-hash-leaf '(:poseidon . 4) leaf)
         (curve-merkle-hash-leaf-psd leaf))
  :enable (crypto-merkle-hash-leaf curve-merkle-hash-leaf-psd
           crypto-poseidon-hash-instance poseidon-hash))

(defruled net-mrk-children-psd
  (equal (crypto-merkle-hash-children '(:poseidon . 2) (list l r))
         (curve-merkle-hash-children-psd l r))
  :enable (crypto-merkle-hash-children curve-merkle-hash-children-psd
           crypto-poseidon-hash-instance poseidon-hash))

(defruled net-mrk-loop-bhp
  (implies (and (fieldp cur) (crypto-field-listp sibs))
           (equal (crypto-merkle-path-loop '(:bhp . 512) bits sibs cur)
                  (curve-merkle-root-bhp bits sibs cur)))
  :induct (curve-merkle-root-bhp bits sibs cur)
  :enable (crypto-merkle-path-loop curve-merkle-root-bhp curve-merkle-order
           net-mrk-children-bhp crypto-field-listp acl2::bfix bitp))

(defruled net-mrk-loop-psd
  (equal (crypto-merkle-path-loop '(:poseidon . 2) bits sibs cur)
         (curve-merkle-root-psd bits sibs cur))
  :induct (curve-merkle-root-psd bits sibs cur)
  :enable (crypto-merkle-path-loop curve-merkle-root-psd curve-merkle-order
           net-mrk-children-psd acl2::bfix bitp))

(defruledl net-mrk-mod-small
  (implies (and (natp n) (natp m) (<= m n) (natp x) (< x (expt 2 m)))
           (equal (mod x (expt 2 n)) x))
  :use (:instance acl2::<=-of-expt-and-expt-same-base-linear (r 2) (i1 m) (i2 n))
  :enable acl2::mod-when-<)

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (local (defthm net-mrk-hi-zero
           (implies (and (natp a) (natp h) (posp e) (< (+ a (* e h)) e))
                    (equal h 0))
           :rule-classes nil
           :hints (("Goal" :nonlinearp t))))
  (local (defthm net-mrk-take-lebits-small
           (implies (and (natp n) (natp m) (<= m n) (natp x) (< x (expt 2 m)))
                    (equal (take m (acl2::nat=>lebits n x))
                           (acl2::nat=>lebits m x)))
           :hints (("Goal"
                    :do-not-induct t
                    :use ((:instance acl2::lebits=>nat-of-append
                                     (acl2::lodigits (take m (acl2::nat=>lebits n x)))
                                     (acl2::hidigits (nthcdr m (acl2::nat=>lebits n x))))
                          (:instance acl2::nat=>lebits-of-lebits=>nat
                                     (acl2::digits (take m (acl2::nat=>lebits n x))))
                          (:instance acl2::lebits=>nat-upper-bound
                                     (acl2::digits (take m (acl2::nat=>lebits n x))))
                          (:instance net-mrk-hi-zero (e (expt 2 m))
                                     (a (acl2::lebits=>nat (take m (acl2::nat=>lebits n x))))
                                     (h (acl2::lebits=>nat (nthcdr m (acl2::nat=>lebits n x))))))
                    :in-theory (disable acl2::lebits=>nat-of-append
                                        acl2::nat=>lebits-of-lebits=>nat)))))
  (defruled net-mrk-take-lebits
    (implies (and (natp n) (natp m) (<= m n) (natp x) (< x (expt 2 m)))
             (equal (take m (acl2::nat=>lebits n (mod x (expt 2 n))))
                    (acl2::nat=>lebits m x)))
    :use (net-mrk-take-lebits-small net-mrk-mod-small)
    :in-theory nil))

(defruled net-mrk-index-bits
  (implies (and (natp depth) (<= depth 64) (natp idx) (< idx (expt 2 depth)))
           (equal (take depth (crypto-nat->lebits 64 idx))
                  (acl2::nat=>lebits depth idx)))
  :enable crypto-nat->lebits
  :use ((:instance net-mrk-take-lebits (n 64) (m depth) (x idx))))

(defruled net-mrk-verify-bhp-is-crypto
  (implies (and (natp leaf-index)
                (crypto-field-listp siblings)
                (fieldp root))
           (equal (aleo-verify-merkle-path-bhp-funspec depth leaf-index siblings root leaf)
                  (crypto-merkle-path-verify '(:bhp . 1024) '(:bhp . 512) depth
                                             (list leaf-index siblings) root leaf)))
  :use (:instance net-mrk-index-bits (depth (nfix depth)) (idx leaf-index))
  :enable (aleo-verify-merkle-path-bhp-funspec crypto-merkle-path-verify
           curve-merkle-path-errorp net-mrk-leaf-bhp net-mrk-loop-bhp))

(defruled net-mrk-verify-psd-is-crypto
  (implies (and (natp leaf-index)
                (fieldp root))
           (equal (aleo-verify-merkle-path-psd-funspec depth leaf-index siblings root leaf)
                  (crypto-merkle-path-verify '(:poseidon . 4) '(:poseidon . 2) depth
                                             (list leaf-index siblings) root leaf)))
  :use (:instance net-mrk-index-bits (depth (nfix depth)) (idx leaf-index))
  :enable (aleo-verify-merkle-path-psd-funspec crypto-merkle-path-verify
           curve-merkle-path-errorp net-mrk-leaf-psd net-mrk-loop-psd))
