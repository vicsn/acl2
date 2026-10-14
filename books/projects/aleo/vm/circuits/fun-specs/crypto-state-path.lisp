; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specification of snarkVM's circuit StatePath::verify
; (circuit/program/src/state_path).

(in-package "ALEOVM")

(include-book "crypto-merkle")

(local (in-theory (disable bitp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Merkle depths (console/program/src/state_path/configuration/mod.rs).

(define crypto-blocks-depth () :returns (n natp) 32)
(define crypto-header-depth () :returns (n natp) 3)
(define crypto-transactions-depth () :returns (n natp) 20)
(define crypto-transaction-depth () :returns (n natp) 5)
(define crypto-transition-depth () :returns (n natp) 5)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Leaves.

; snarkVM circuit/program/src/state_path/helpers/header_leaf.rs: (index: u8, id: field).
(define crypto-header-leaf-p (x)
  :returns (yes/no booleanp)
  (and (true-listp x)
       (equal (len x) 2)
       (natp (first x)) (< (first x) 256)
       (fieldp (second x))))

; snarkVM circuit/program/src/state_path/helpers/header_leaf.rs: HeaderLeaf::write_bits_le.
(define crypto-header-leaf-bits-le ((leaf crypto-header-leaf-p))
  :returns (bits bit-listp)
  (b* (((list index id) leaf))
    (append (crypto-nat->lebits 8 index)
            (crypto-field-bits-le id)))
  :guard-hints (("Goal" :in-theory (enable crypto-header-leaf-p))))

; snarkVM circuit/program/src/state_path/helpers/transaction_leaf.rs:
; (variant: u8, index: u16, id: field).
(define crypto-transaction-leaf-p (x)
  :returns (yes/no booleanp)
  (and (true-listp x)
       (equal (len x) 3)
       (natp (first x)) (< (first x) 256)
       (natp (second x)) (< (second x) 65536)
       (fieldp (third x))))

; snarkVM circuit/program/src/state_path/helpers/transaction_leaf.rs:
; TransactionLeaf::write_bits_le.
(define crypto-transaction-leaf-bits-le ((leaf crypto-transaction-leaf-p))
  :returns (bits bit-listp)
  (b* (((list variant index id) leaf))
    (append (crypto-nat->lebits 8 variant)
            (crypto-nat->lebits 16 index)
            (crypto-field-bits-le id)))
  :guard-hints (("Goal" :in-theory (enable crypto-transaction-leaf-p))))

; snarkVM circuit/program/src/state_path/helpers/transition_leaf.rs:
; (version: u8, index: u8, variant: u8, id: field).
(define crypto-transition-leaf-p (x)
  :returns (yes/no booleanp)
  (and (true-listp x)
       (equal (len x) 4)
       (natp (first x)) (< (first x) 256)
       (natp (second x)) (< (second x) 256)
       (natp (third x)) (< (third x) 256)
       (fieldp (fourth x))))

; snarkVM circuit/program/src/state_path/helpers/transition_leaf.rs:
; TransitionLeaf::write_bits_le.
(define crypto-transition-leaf-bits-le ((leaf crypto-transition-leaf-p))
  :returns (bits bit-listp)
  (b* (((list version index variant id) leaf))
    (append (crypto-nat->lebits 8 version)
            (crypto-nat->lebits 8 index)
            (crypto-nat->lebits 8 variant)
            (crypto-field-bits-le id)))
  :guard-hints (("Goal" :in-theory (enable crypto-transition-leaf-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; State paths.

; snarkVM circuit/program/src/state_path/mod.rs: StatePath, as the list
; (global-state-root block-path block-hash previous-block-hash header-root
;  header-path header-leaf transactions-path transaction-id transaction-path
;  transaction-leaf transition-root tcm transition-path transition-leaf).
(define crypto-state-path-p (x)
  :returns (yes/no booleanp)
  (and (true-listp x)
       (equal (len x) 15)
       (fieldp (nth 0 x))
       (crypto-merkle-path-p (nth 1 x))
       (fieldp (nth 2 x))
       (fieldp (nth 3 x))
       (fieldp (nth 4 x))
       (crypto-merkle-path-p (nth 5 x))
       (crypto-header-leaf-p (nth 6 x))
       (crypto-merkle-path-p (nth 7 x))
       (fieldp (nth 8 x))
       (crypto-merkle-path-p (nth 9 x))
       (crypto-transaction-leaf-p (nth 10 x))
       (fieldp (nth 11 x))
       (fieldp (nth 12 x))
       (crypto-merkle-path-p (nth 13 x))
       (crypto-transition-leaf-p (nth 14 x))))

; snarkVM circuit/network/src/v0.rs: AleoV0::verify_merkle_path_bhp
; (leaf hasher BHP1024, path hasher BHP512).
(define crypto-verify-merkle-path-bhp ((depth natp)
                                       (path crypto-merkle-path-p)
                                       (root fieldp)
                                       (leaf bit-listp))
  :returns (r (implies (not (reserrp r)) (bitp r)))
  (crypto-merkle-path-verify '(:bhp . 1024) '(:bhp . 512) depth path root leaf)
  :guard-hints (("Goal" :in-theory (enable crypto-field-hasher-p
                                           crypto-merkle-leaf-p))))

; snarkVM circuit/network/src/v0.rs: AleoV0::verify_merkle_path_psd
; (leaf hasher Poseidon4, path hasher Poseidon2).
(define crypto-verify-merkle-path-psd ((depth natp)
                                       (path crypto-merkle-path-p)
                                       (root fieldp)
                                       (leaf crypto-field-listp))
  :returns (r (implies (not (reserrp r)) (bitp r)))
  (crypto-merkle-path-verify '(:poseidon . 4) '(:poseidon . 2) depth path root leaf)
  :guard-hints (("Goal" :in-theory (enable crypto-field-hasher-p
                                           crypto-merkle-leaf-p))))

; snarkVM circuit/program/src/state_path/verify.rs: StatePath::verify.
; Every Merkle path is verified (and may halt) regardless of is_global;
; the result is the global check if is_global, else the local check.
(define crypto-state-path-verify ((state-path crypto-state-path-p)
                                  (is-global bitp)
                                  (local-state-root fieldp))
  :returns (r (implies (not (reserrp r)) (bitp r)))
  (b* (((list global-state-root block-path block-hash previous-block-hash
              header-root header-path header-leaf transactions-path
              transaction-id transaction-path transaction-leaf
              transition-root tcm transition-path transition-leaf)
        state-path)
       ;; Transition path; variant 3 = Input::Record.
       ((fty::ok v) (crypto-verify-merkle-path-bhp
                (crypto-transition-depth) transition-path transition-root
                (crypto-transition-leaf-bits-le transition-leaf)))
       (check-transition-path
        (crypto-bit-and v (crypto-bit-eq (third transition-leaf) 3)))
       ;; Transaction leaf id = BHP512(transition_root || tcm).
       (check-transaction-leaf
        (crypto-bit-eq (crypto-hash-bhp 512
                                        (append (crypto-field-bits-le transition-root)
                                                (crypto-field-bits-le tcm)))
                       (third transaction-leaf)))
       ;; Transaction path; variant 1 = Transaction::Execution.
       ((fty::ok v) (crypto-verify-merkle-path-bhp
                (crypto-transaction-depth) transaction-path transaction-id
                (crypto-transaction-leaf-bits-le transaction-leaf)))
       (check-transaction-path
        (crypto-bit-and v (crypto-bit-eq (first transaction-leaf) 1)))
       ;; Transactions path, rooted at the header leaf id.
       ((fty::ok check-transactions-path)
        (crypto-verify-merkle-path-bhp
         (crypto-transactions-depth) transactions-path (second header-leaf)
         (crypto-field-bits-le transaction-id)))
       ;; Header path; index 1 = Header::transactions_root.
       ((fty::ok v) (crypto-verify-merkle-path-bhp
                (crypto-header-depth) header-path header-root
                (crypto-header-leaf-bits-le header-leaf)))
       (check-header-path
        (crypto-bit-and v (crypto-bit-eq (first header-leaf) 1)))
       ;; Block hash = BHP1024(previous_block_hash || header_root).
       (check-block-hash
        (crypto-bit-eq (crypto-hash-bhp 1024
                                        (append (crypto-field-bits-le previous-block-hash)
                                                (crypto-field-bits-le header-root)))
                       block-hash))
       ;; Block path, rooted at the global state root.
       ((fty::ok check-state-root)
        (crypto-verify-merkle-path-bhp
         (crypto-blocks-depth) block-path global-state-root
         (crypto-field-bits-le block-hash)))
       (check-transition-and-transaction-path
        (crypto-bit-and (crypto-bit-and check-transition-path
                                        check-transaction-path)
                        check-transaction-leaf))
       (check-local
        (crypto-bit-and check-transition-and-transaction-path
                        (crypto-bit-eq local-state-root transaction-id)))
       (check-global
        (crypto-bit-and
         (crypto-bit-and
          (crypto-bit-and
           (crypto-bit-and check-transition-and-transaction-path
                           check-transactions-path)
           check-header-path)
          check-block-hash)
         check-state-root)))
    (if (equal is-global 1) check-global check-local))
  :guard-hints (("Goal" :in-theory (enable crypto-state-path-p
                                           crypto-header-leaf-p
                                           crypto-transaction-leaf-p
                                           crypto-transition-leaf-p))))
