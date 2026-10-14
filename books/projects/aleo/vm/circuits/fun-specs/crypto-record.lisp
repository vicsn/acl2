; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specifications of snarkVM's circuit Ciphertext, Owner, and Record
; (circuit/program/src/data/{ciphertext,record}).
;
; Plaintext records are values-model.lisp records; ciphertext records are
; crypto-ciphertext-records (crypto-values.lisp).  Ciphertexts are lists of
; field elements.  Group-valued intermediate results (scalar multiples) are
; Edwards-BLS12 points.

(in-package "ALEOVM")

(include-book "crypto-values")

(local (include-book "arithmetic-5/top" :dir :system))

(local (in-theory (disable bitp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Field-list helpers.

(define crypto-field-list-add ((xs values-field-listp) (ys values-field-listp))
  :guard (equal (len xs) (len ys))
  :returns (zs values-field-listp)
  (if (or (endp xs) (endp ys))
      nil
    (cons (crypto-field-add (car xs) (car ys))
          (crypto-field-list-add (cdr xs) (cdr ys)))))

(define crypto-field-list-sub ((xs values-field-listp) (ys values-field-listp))
  :guard (equal (len xs) (len ys))
  :returns (zs values-field-listp)
  (if (or (endp xs) (endp ys))
      nil
    (cons (crypto-field-sub (car xs) (car ys))
          (crypto-field-list-sub (cdr xs) (cdr ys)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Ciphertext.

; snarkVM circuit/program/src/data/ciphertext/mod.rs: Ciphertext::new (Inject).
(define crypto-ciphertext-new ((fields values-field-listp))
  :returns (c (implies (not (reserrp c)) (values-field-listp c)))
  (if (<= (len fields) (crypto-max-data-size-in-fields))
      (values-field-list-fix fields)
    (spec-error)))

; snarkVM circuit/program/src/data/ciphertext/to_bits.rs: Ciphertext::write_bits_le.
(define crypto-ciphertext-write-bits-le ((c values-field-listp))
  :returns (bits bit-listp)
  (crypto-field-list-bits-le c))

; snarkVM circuit/program/src/data/ciphertext/to_bits.rs: Ciphertext::write_bits_be.
(define crypto-ciphertext-write-bits-be ((c values-field-listp))
  :returns (bits bit-listp)
  (crypto-field-list-bits-be c))

; snarkVM circuit/program/src/data/ciphertext/equal.rs: Ciphertext::is_equal.
(define crypto-ciphertext-is-equal ((a values-field-listp) (b values-field-listp))
  :returns (r bitp)
  (cond ((not (equal (len a) (len b))) 0)
        ((equal (values-field-list-fix a) (values-field-list-fix b)) 1)
        (t 0)))

; snarkVM circuit/program/src/data/ciphertext/equal.rs: Ciphertext::is_not_equal.
(define crypto-ciphertext-is-not-equal ((a values-field-listp) (b values-field-listp))
  :returns (r bitp)
  (crypto-bit-not (crypto-ciphertext-is-equal a b)))

; snarkVM circuit/program/src/data/ciphertext/size_in_fields.rs: Ciphertext::size_in_fields
; (also Ciphertext::num_randomizers).
(define crypto-ciphertext-size-in-fields ((c values-field-listp))
  :returns (n (implies (not (reserrp n)) (natp n)))
  (if (<= (len c) (crypto-max-data-size-in-fields))
      (len c)
    (spec-error))
  ///
  (defret crypto-ciphertext-size-in-fields-natp-or-consp
    (or (natp n) (consp n))
    :rule-classes :type-prescription))

; snarkVM circuit/program/src/data/ciphertext/decrypt.rs: Ciphertext::decrypt_with_randomizers
; (zip_eq halts on a length mismatch).
(define crypto-ciphertext-decrypt-with-randomizers ((c values-field-listp)
                                                    (randomizers values-field-listp))
  :returns (p plaintext-resultp)
  (if (equal (len c) (len randomizers))
      (crypto-plaintext-from-fields (crypto-field-list-sub c randomizers))
    (spec-error)))

; snarkVM circuit/program/src/data/ciphertext/decrypt.rs: Ciphertext::decrypt_symmetric.
(define crypto-ciphertext-decrypt-symmetric ((c values-field-listp)
                                             (plaintext-view-key fieldp))
  :returns (p plaintext-resultp)
  (b* (((fty::ok n) (crypto-ciphertext-size-in-fields c))
       (n (nfix n))
       (randomizers (crypto-hash-many-psd
                     8 (list (crypto-encryption-domain) plaintext-view-key) n)))
    (crypto-ciphertext-decrypt-with-randomizers c randomizers)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Plaintext encryption (used by records, requests, and responses).

; snarkVM circuit/program/src/data/plaintext/encrypt.rs: Plaintext::encrypt_with_randomizers.
(define crypto-plaintext-encrypt-with-randomizers ((p plaintextp)
                                                   (randomizers values-field-listp))
  :returns (c (implies (not (reserrp c)) (values-field-listp c)))
  (b* (((fty::ok fields) (crypto-plaintext-to-fields p))
       ((unless (equal (len fields) (len randomizers))) (spec-error)))
    (crypto-ciphertext-new (crypto-field-list-add fields randomizers))))

; snarkVM circuit/program/src/data/plaintext/encrypt.rs: Plaintext::encrypt_symmetric.
(define crypto-plaintext-encrypt-symmetric ((p plaintextp) (plaintext-view-key fieldp))
  :returns (c (implies (not (reserrp c)) (values-field-listp c)))
  (b* (((fty::ok n) (crypto-plaintext-size-in-fields p))
       (n (nfix n))
       (randomizers (crypto-hash-many-psd
                     8 (list (crypto-encryption-domain) plaintext-view-key) n)))
    (crypto-plaintext-encrypt-with-randomizers p randomizers)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Owner.

; snarkVM circuit/program/src/data/record/helpers/owner.rs: Owner::<Plaintext>::new (Inject).
; The console owner is public (an address) or private (a plaintext);
; a private owner that is not an address literal halts.
(define crypto-owner-new ((publicp booleanp) x)
  :guard (if publicp (groupp x) (plaintextp x))
  :returns (o owner-resultp)
  (if publicp
      (owner-public x)
    (if (and (plaintext-case x :literal)
             (literal-case (plaintext-literal->get x) :address))
        (owner-private (literal-address->get (plaintext-literal->get x)))
      (spec-error))))

; snarkVM circuit/program/src/data/record/helpers/owner.rs: Owner::to_entry.
(define crypto-owner-to-entry ((o ownerp))
  :returns (e entryp)
  (owner-case o
    :public (entry-public (plaintext-literal (literal-address o.address)))
    :private (entry-private (plaintext-literal (literal-address o.address)))))

; The address of an owner (Deref for Owner<A, Plaintext<A>>).
(define crypto-owner-address ((o ownerp))
  :returns (a groupp)
  (owner-case o
    :public o.address
    :private o.address))

(define crypto-owner-privatep ((o ownerp))
  :returns (b bitp)
  (if (owner-case o :private) 1 0))

; snarkVM circuit/program/src/data/record/helpers/owner.rs: Owner::is_equal
; (Owner<A, Plaintext<A>>; a private owner is an address literal).
(define crypto-owner-is-equal ((a ownerp) (b ownerp))
  :returns (r bitp)
  (cond ((and (owner-case a :public) (owner-case b :public))
         (if (equal (owner-public->address a) (owner-public->address b)) 1 0))
        ((and (owner-case a :private) (owner-case b :private))
         (crypto-plaintext-is-equal
          (plaintext-literal (literal-address (owner-private->address a)))
          (plaintext-literal (literal-address (owner-private->address b)))))
        (t 0)))

; snarkVM circuit/program/src/data/record/helpers/owner.rs: Owner::is_not_equal.
(define crypto-owner-is-not-equal ((a ownerp) (b ownerp))
  :returns (r bitp)
  (crypto-bit-not (crypto-owner-is-equal a b)))

; snarkVM circuit/program/src/data/record/helpers/owner.rs: Owner::is_equal
; (Owner<A, Ciphertext<A>>).
(define crypto-ciphertext-owner-is-equal ((a crypto-ciphertext-ownerp)
                                          (b crypto-ciphertext-ownerp))
  :returns (r bitp)
  (cond ((and (crypto-ciphertext-owner-case a :public)
              (crypto-ciphertext-owner-case b :public))
         (if (equal (crypto-ciphertext-owner-public->address a)
                    (crypto-ciphertext-owner-public->address b))
             1 0))
        ((and (crypto-ciphertext-owner-case a :private)
              (crypto-ciphertext-owner-case b :private))
         (crypto-ciphertext-is-equal (crypto-ciphertext-owner-private->ciphertext a)
                                     (crypto-ciphertext-owner-private->ciphertext b)))
        (t 0)))

; snarkVM circuit/program/src/data/record/helpers/owner.rs: Owner::is_not_equal
; (Owner<A, Ciphertext<A>>).
(define crypto-ciphertext-owner-is-not-equal ((a crypto-ciphertext-ownerp)
                                              (b crypto-ciphertext-ownerp))
  :returns (r bitp)
  (crypto-bit-not (crypto-ciphertext-owner-is-equal a b)))

; snarkVM circuit/program/src/data/record/helpers/owner.rs: Owner::encrypt.
; A public owner takes no randomizer; a private owner takes one and is
; encrypted as the address x-coordinate plus the randomizer.
(define crypto-owner-encrypt ((o ownerp) (randomizers values-field-listp))
  :returns (c crypto-ciphertext-owner-resultp)
  (owner-case o
    :public (if (endp randomizers)
                (crypto-ciphertext-owner-public o.address)
              (spec-error))
    :private (if (equal (len randomizers) 1)
                 (crypto-ciphertext-owner-private
                  (list (crypto-field-add (crypto-group-x o.address)
                                          (car randomizers))))
               (spec-error))))

; snarkVM circuit/program/src/data/record/helpers/owner.rs: Owner::decrypt.
; A private owner needs one randomizer and a one-field ciphertext; the address
; is recovered with Address::from_field (Group::from_x_coordinate).
(define crypto-owner-decrypt ((c crypto-ciphertext-ownerp) (randomizers values-field-listp))
  :returns (o owner-resultp)
  (crypto-ciphertext-owner-case c
    :public (if (endp randomizers)
                (owner-public c.address)
              (spec-error))
    :private (b* (((unless (equal (len randomizers) 1)) (spec-error))
                  ((unless (equal (len c.ciphertext) 1)) (spec-error))
                  ((fty::ok address) (crypto-group-from-x
                                 (crypto-field-sub (car c.ciphertext)
                                                   (car randomizers)))))
               (owner-private address))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Entries.

; snarkVM circuit/program/src/data/record/entry/to_bits.rs: the visibility bits
; (constant = [false, false], public = [false, true], private = [true, false]).
(define crypto-entry-visibility-bits (kind)
  :returns (bits bit-listp)
  (case kind
    (:constant (list 0 0))
    (:public (list 0 1))
    (otherwise (list 1 0))))

; snarkVM circuit/program/src/data/record/entry/to_bits.rs: Entry::<Plaintext>::write_bits_le.
(define crypto-entry-bits-le ((e entryp))
  :returns (bits bit-listp)
  (append (crypto-entry-visibility-bits (entry-kind e))
          (entry-case e
            :constant (crypto-plaintext-bits-le e.get)
            :public (crypto-plaintext-bits-le e.get)
            :private (crypto-plaintext-bits-le e.get))))

; snarkVM circuit/program/src/data/record/entry/to_bits.rs: Entry::<Plaintext>::write_bits_be.
(define crypto-entry-bits-be ((e entryp))
  :returns (bits bit-listp)
  (append (crypto-entry-visibility-bits (entry-kind e))
          (entry-case e
            :constant (crypto-plaintext-bits-be e.get)
            :public (crypto-plaintext-bits-be e.get)
            :private (crypto-plaintext-bits-be e.get))))

; snarkVM circuit/program/src/data/record/entry/to_bits.rs: Entry::<Ciphertext>::write_bits_le.
(define crypto-ciphertext-entry-bits-le ((e crypto-ciphertext-entryp))
  :returns (bits bit-listp)
  (append (crypto-entry-visibility-bits (crypto-ciphertext-entry-kind e))
          (crypto-ciphertext-entry-case e
            :constant (crypto-plaintext-bits-le e.get)
            :public (crypto-plaintext-bits-le e.get)
            :private (crypto-ciphertext-write-bits-le e.get))))

; snarkVM circuit/program/src/data/record/entry/to_bits.rs: Entry::<Ciphertext>::write_bits_be.
(define crypto-ciphertext-entry-bits-be ((e crypto-ciphertext-entryp))
  :returns (bits bit-listp)
  (append (crypto-entry-visibility-bits (crypto-ciphertext-entry-kind e))
          (crypto-ciphertext-entry-case e
            :constant (crypto-plaintext-bits-be e.get)
            :public (crypto-plaintext-bits-be e.get)
            :private (crypto-ciphertext-write-bits-be e.get))))

; snarkVM circuit/program/src/data/record/entry/num_randomizers.rs: Entry::<Plaintext>::num_randomizers.
(define crypto-entry-num-randomizers ((e entryp))
  :returns (n (implies (not (reserrp n)) (natp n)))
  (entry-case e
    :constant 0
    :public 0
    :private (crypto-plaintext-size-in-fields e.get))
  ///
  (defret crypto-entry-num-randomizers-natp-or-consp
    (or (natp n) (consp n))
    :rule-classes :type-prescription))

; snarkVM circuit/program/src/data/record/entry/num_randomizers.rs: Entry::<Ciphertext>::num_randomizers.
(define crypto-ciphertext-entry-num-randomizers ((e crypto-ciphertext-entryp))
  :returns (n (implies (not (reserrp n)) (natp n)))
  (crypto-ciphertext-entry-case e
    :constant 0
    :public 0
    :private (crypto-ciphertext-size-in-fields e.get))
  ///
  (defret crypto-ciphertext-entry-num-randomizers-natp-or-consp
    (or (natp n) (consp n))
    :rule-classes :type-prescription))

; snarkVM circuit/program/src/data/record/entry/equal.rs: Entry::is_equal (Plaintext).
(define crypto-entry-is-equal ((a entryp) (b entryp))
  :returns (r bitp)
  (if (equal (entry-kind a) (entry-kind b))
      (crypto-plaintext-is-equal (entry-case a
                                   :constant a.get
                                   :public a.get
                                   :private a.get)
                                 (entry-case b
                                   :constant b.get
                                   :public b.get
                                   :private b.get))
    0))

; snarkVM circuit/program/src/data/record/entry/equal.rs: Entry::is_equal (Ciphertext).
(define crypto-ciphertext-entry-is-equal ((a crypto-ciphertext-entryp)
                                          (b crypto-ciphertext-entryp))
  :returns (r bitp)
  (cond ((not (equal (crypto-ciphertext-entry-kind a)
                     (crypto-ciphertext-entry-kind b)))
         0)
        ((crypto-ciphertext-entry-case a :private)
         (crypto-ciphertext-is-equal (crypto-ciphertext-entry-private->get a)
                                     (crypto-ciphertext-entry-private->get b)))
        (t (crypto-plaintext-is-equal
            (if (crypto-ciphertext-entry-case a :constant)
                (crypto-ciphertext-entry-constant->get a)
              (crypto-ciphertext-entry-public->get a))
            (if (crypto-ciphertext-entry-case b :constant)
                (crypto-ciphertext-entry-constant->get b)
              (crypto-ciphertext-entry-public->get b))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Record construction and simple queries.

; snarkVM circuit/program/src/data/record/mod.rs: Record::<Plaintext>::new (Inject):
; the owner is injected with Owner::new, the other components unchanged.
(define crypto-record-new ((owner-publicp booleanp)
                           owner
                           (data record-entry-listp)
                           (nonce groupp)
                           (version acl2::ubyte8p))
  :guard (if owner-publicp (groupp owner) (plaintextp owner))
  :returns (r record-resultp)
  (b* (((fty::ok owner) (crypto-owner-new owner-publicp owner)))
    (record owner data nonce version)))

; snarkVM circuit/program/src/data/record/mod.rs: Record::<Ciphertext>::new (Inject):
; Ciphertext::new halts on ciphertexts longer than MAX_DATA_SIZE_IN_FIELDS.
(define crypto-ciphertext-record-new ((r crypto-ciphertext-recordp))
  :returns (r1 crypto-ciphertext-record-resultp)
  (b* ((owner (crypto-ciphertext-record->owner r))
       ((when (and (crypto-ciphertext-owner-case owner :private)
                   (reserrp (crypto-ciphertext-new
                             (crypto-ciphertext-owner-private->ciphertext owner)))))
        (spec-error))
       ((unless (crypto-ciphertext-entries-ok (crypto-ciphertext-record->data r)))
        (spec-error)))
    (crypto-ciphertext-record-fix r))
  :prepwork
  ((define crypto-ciphertext-entries-ok ((data crypto-ciphertext-record-entry-listp))
     :returns (yes/no booleanp)
     (b* (((when (endp data)) t)
          (e (crypto-ciphertext-record-entry->entry (car data))))
       (and (or (not (crypto-ciphertext-entry-case e :private))
                (not (reserrp (crypto-ciphertext-new
                               (crypto-ciphertext-entry-private->get e)))))
            (crypto-ciphertext-entries-ok (cdr data)))))))

; snarkVM circuit/program/src/data/record/mod.rs: Record::is_hiding (version != 0).
(define crypto-record-is-hiding ((version acl2::ubyte8p))
  :returns (b bitp)
  (if (equal (acl2::ubyte8-fix version) 0) 0 1))

; Sum of the entries' randomizers, halting as soon as the u16 sum overflows.
(define crypto-record-entries-num-randomizers ((data record-entry-listp) (acc natp))
  :returns (n (implies (not (reserrp n)) (natp n)))
  (b* (((when (endp data)) (lnfix acc))
       ((fty::ok k) (crypto-entry-num-randomizers (record-entry->entry (car data))))
       (k (nfix k))
       (acc (+ (lnfix acc) (nfix k)))
       ((when (>= acc 65536)) (spec-error)))
    (crypto-record-entries-num-randomizers (cdr data) acc))
  ///
  (defret crypto-record-entries-num-randomizers-natp-or-consp
    (or (natp n) (consp n))
    :rule-classes :type-prescription))

; snarkVM circuit/program/src/data/record/num_randomizers.rs: Record::<Plaintext>::num_randomizers.
(define crypto-record-num-randomizers ((r recordp))
  :returns (n (implies (not (reserrp n)) (natp n)))
  (b* (((fty::ok n) (crypto-record-entries-num-randomizers
                (record->data r)
                (crypto-owner-privatep (record->owner r))))
       (n (nfix n))
       ((when (> n (crypto-max-data-size-in-fields))) (spec-error)))
    n)
  ///
  (defret crypto-record-num-randomizers-natp-or-consp
    (or (natp n) (consp n))
    :rule-classes :type-prescription))

(define crypto-ciphertext-record-entries-num-randomizers
  ((data crypto-ciphertext-record-entry-listp) (acc natp))
  :returns (n (implies (not (reserrp n)) (natp n)))
  (b* (((when (endp data)) (lnfix acc))
       ((fty::ok k) (crypto-ciphertext-entry-num-randomizers
                (crypto-ciphertext-record-entry->entry (car data))))
       (k (nfix k))
       (acc (+ (lnfix acc) (nfix k)))
       ((when (>= acc 65536)) (spec-error)))
    (crypto-ciphertext-record-entries-num-randomizers (cdr data) acc))
  ///
  (defret crypto-ciphertext-record-entries-num-randomizers-natp-or-consp
    (or (natp n) (consp n))
    :rule-classes :type-prescription))

; snarkVM circuit/program/src/data/record/num_randomizers.rs:
; Record::<Ciphertext>::num_randomizers.
(define crypto-ciphertext-record-num-randomizers ((r crypto-ciphertext-recordp))
  :returns (n (implies (not (reserrp n)) (natp n)))
  (b* ((owner (crypto-ciphertext-record->owner r))
       ((fty::ok n) (crypto-ciphertext-record-entries-num-randomizers
                (crypto-ciphertext-record->data r)
                (if (crypto-ciphertext-owner-case owner :private) 1 0)))
       (n (nfix n))
       ((when (> n (crypto-max-data-size-in-fields))) (spec-error)))
    n)
  ///
  (defret crypto-ciphertext-record-num-randomizers-natp-or-consp
    (or (natp n) (consp n))
    :rule-classes :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Record bits and fields.

(define crypto-record-data-bits-le ((data record-entry-listp))
  :returns (bits bit-listp)
  (if (endp data)
      nil
    (append (crypto-identifier-bits-le (record-entry->name (car data)))
            (crypto-entry-bits-le (record-entry->entry (car data)))
            (crypto-record-data-bits-le (cdr data)))))

(define crypto-record-data-bits-be ((data record-entry-listp))
  :returns (bits bit-listp)
  (if (endp data)
      nil
    (append (crypto-identifier-bits-be (record-entry->name (car data)))
            (crypto-entry-bits-be (record-entry->entry (car data)))
            (crypto-record-data-bits-be (cdr data)))))

(define crypto-ciphertext-record-data-bits-le ((data crypto-ciphertext-record-entry-listp))
  :returns (bits bit-listp)
  (if (endp data)
      nil
    (append (crypto-identifier-bits-le
             (crypto-ciphertext-record-entry->name (car data)))
            (crypto-ciphertext-entry-bits-le
             (crypto-ciphertext-record-entry->entry (car data)))
            (crypto-ciphertext-record-data-bits-le (cdr data)))))

(define crypto-ciphertext-record-data-bits-be ((data crypto-ciphertext-record-entry-listp))
  :returns (bits bit-listp)
  (if (endp data)
      nil
    (append (crypto-identifier-bits-be
             (crypto-ciphertext-record-entry->name (car data)))
            (crypto-ciphertext-entry-bits-be
             (crypto-ciphertext-record-entry->entry (car data)))
            (crypto-ciphertext-record-data-bits-be (cdr data)))))

; The common layout of Record::write_bits_le:
; is_private || owner || 31 low bits of the data length || is_hiding || data
; || nonce || version.  Halts if the data has 2^31 bits or more.
(define crypto-record-layout-bits-le ((owner-privatep bitp)
                                      (owner-bits bit-listp)
                                      (data-bits bit-listp)
                                      (nonce groupp)
                                      (version acl2::ubyte8p))
  :returns (bits bit-list-resultp :hyp :guard)
  (if (>= (len data-bits) (expt 2 31))
      (spec-error)
    (append (list owner-privatep)
            owner-bits
            (take 31 (crypto-nat->lebits 32 (len data-bits)))
            (list (crypto-record-is-hiding version))
            data-bits
            (crypto-group-bits-le nonce)
            (crypto-nat->lebits 8 (acl2::ubyte8-fix version))))
  ///
  (defret bit-listp-of-crypto-record-layout-bits-le
    (implies (not (reserrp bits)) (bit-listp bits))
    :hyp :guard))

; The common layout of Record::write_bits_be:
; is_private || owner || is_hiding || 31 low bits of the data length (big-endian,
; i.e. the u32 big-endian bits without the first) || data || nonce || version.
(define crypto-record-layout-bits-be ((owner-privatep bitp)
                                      (owner-bits bit-listp)
                                      (data-bits bit-listp)
                                      (nonce groupp)
                                      (version acl2::ubyte8p))
  :returns (bits bit-list-resultp :hyp :guard)
  (if (>= (len data-bits) (expt 2 31))
      (spec-error)
    (append (list owner-privatep)
            owner-bits
            (list (crypto-record-is-hiding version))
            (nthcdr 1 (crypto-nat->bebits 32 (len data-bits)))
            data-bits
            (crypto-group-bits-be nonce)
            (crypto-nat->bebits 8 (acl2::ubyte8-fix version))))
  ///
  (defret bit-listp-of-crypto-record-layout-bits-be
    (implies (not (reserrp bits)) (bit-listp bits))
    :hyp :guard))

; snarkVM circuit/program/src/data/record/to_bits.rs: Record::<Plaintext>::write_bits_le.
(define crypto-record-write-bits-le ((r recordp))
  :returns (bits bit-list-resultp)
  (b* ((owner (record->owner r)))
    (crypto-record-layout-bits-le (crypto-owner-privatep owner)
                                  (crypto-group-bits-le (crypto-owner-address owner))
                                  (crypto-record-data-bits-le (record->data r))
                                  (record->nonce r)
                                  (record->version r)))
  ///
  (defret bit-listp-of-crypto-record-write-bits-le
    (implies (not (reserrp bits)) (bit-listp bits))))

; snarkVM circuit/program/src/data/record/to_bits.rs: Record::<Plaintext>::write_bits_be.
(define crypto-record-write-bits-be ((r recordp))
  :returns (bits bit-list-resultp)
  (b* ((owner (record->owner r)))
    (crypto-record-layout-bits-be (crypto-owner-privatep owner)
                                  (crypto-group-bits-be (crypto-owner-address owner))
                                  (crypto-record-data-bits-be (record->data r))
                                  (record->nonce r)
                                  (record->version r)))
  ///
  (defret bit-listp-of-crypto-record-write-bits-be
    (implies (not (reserrp bits)) (bit-listp bits))))

; snarkVM circuit/program/src/data/record/to_bits.rs: Record::<Ciphertext>::write_bits_le
; (a private owner must be a one-field ciphertext).
(define crypto-ciphertext-record-write-bits-le ((r crypto-ciphertext-recordp))
  :returns (bits bit-list-resultp)
  (b* ((owner (crypto-ciphertext-record->owner r))
       ((fty::ok owner-bits)
        (crypto-ciphertext-owner-case owner
          :public (crypto-group-bits-le owner.address)
          :private (if (equal (len owner.ciphertext) 1)
                       (crypto-field-bits-le (car owner.ciphertext))
                     (spec-error)))))
    (crypto-record-layout-bits-le (if (crypto-ciphertext-owner-case owner :private) 1 0)
                                  owner-bits
                                  (crypto-ciphertext-record-data-bits-le
                                   (crypto-ciphertext-record->data r))
                                  (crypto-ciphertext-record->nonce r)
                                  (crypto-ciphertext-record->version r)))
  ///
  (defret bit-listp-of-crypto-ciphertext-record-write-bits-le
    (implies (not (reserrp bits)) (bit-listp bits))))

; snarkVM circuit/program/src/data/record/to_bits.rs: Record::<Ciphertext>::write_bits_be.
(define crypto-ciphertext-record-write-bits-be ((r crypto-ciphertext-recordp))
  :returns (bits bit-list-resultp)
  (b* ((owner (crypto-ciphertext-record->owner r))
       ((fty::ok owner-bits)
        (crypto-ciphertext-owner-case owner
          :public (crypto-group-bits-be owner.address)
          :private (if (equal (len owner.ciphertext) 1)
                       (crypto-field-bits-be (car owner.ciphertext))
                     (spec-error)))))
    (crypto-record-layout-bits-be (if (crypto-ciphertext-owner-case owner :private) 1 0)
                                  owner-bits
                                  (crypto-ciphertext-record-data-bits-be
                                   (crypto-ciphertext-record->data r))
                                  (crypto-ciphertext-record->nonce r)
                                  (crypto-ciphertext-record->version r)))
  ///
  (defret bit-listp-of-crypto-ciphertext-record-write-bits-be
    (implies (not (reserrp bits)) (bit-listp bits))))

; snarkVM circuit/program/src/data/record/to_fields.rs: Record::<Plaintext>::to_fields.
(define crypto-record-to-fields ((r recordp))
  :returns (fields (implies (not (reserrp fields)) (values-field-listp fields)))
  (b* (((fty::ok bits) (crypto-record-write-bits-le r)))
    (crypto-bits-to-fields-checked bits)))

; snarkVM circuit/program/src/data/record/to_fields.rs: Record::<Ciphertext>::to_fields.
(define crypto-ciphertext-record-to-fields ((r crypto-ciphertext-recordp))
  :returns (fields (implies (not (reserrp fields)) (values-field-listp fields)))
  (b* (((fty::ok bits) (crypto-ciphertext-record-write-bits-le r)))
    (crypto-bits-to-fields-checked bits)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Record equality.

(define crypto-record-data-is-equal ((a record-entry-listp) (b record-entry-listp))
  :guard (equal (len a) (len b))
  :returns (r bitp)
  (if (or (endp a) (endp b))
      1
    (crypto-bit-and
     (crypto-bit-and (crypto-bit-eq (record-entry->name (car a))
                                    (record-entry->name (car b)))
                     (crypto-entry-is-equal (record-entry->entry (car a))
                                            (record-entry->entry (car b))))
     (crypto-record-data-is-equal (cdr a) (cdr b)))))

; snarkVM circuit/program/src/data/record/equal.rs: Record::is_equal (Plaintext):
; records with different numbers of entries are unequal; otherwise the owners,
; entry names, entries, nonces, and versions are compared and conjoined.
(define crypto-record-is-equal ((a recordp) (b recordp))
  :returns (r bitp)
  (b* (((unless (equal (len (record->data a)) (len (record->data b)))) 0))
    (crypto-bit-and
     (crypto-bit-and
      (crypto-bit-and (crypto-owner-is-equal (record->owner a) (record->owner b))
                      (crypto-record-data-is-equal (record->data a) (record->data b)))
      (crypto-bit-eq (record->nonce a) (record->nonce b)))
     (crypto-bit-eq (record->version a) (record->version b)))))

; snarkVM circuit/program/src/data/record/equal.rs: Record::is_not_equal (Plaintext).
(define crypto-record-is-not-equal ((a recordp) (b recordp))
  :returns (r bitp)
  (crypto-bit-not (crypto-record-is-equal a b)))

(define crypto-ciphertext-record-data-is-equal ((a crypto-ciphertext-record-entry-listp)
                                                (b crypto-ciphertext-record-entry-listp))
  :guard (equal (len a) (len b))
  :returns (r bitp)
  (if (or (endp a) (endp b))
      1
    (crypto-bit-and
     (crypto-bit-and (crypto-bit-eq (crypto-ciphertext-record-entry->name (car a))
                                    (crypto-ciphertext-record-entry->name (car b)))
                     (crypto-ciphertext-entry-is-equal
                      (crypto-ciphertext-record-entry->entry (car a))
                      (crypto-ciphertext-record-entry->entry (car b))))
     (crypto-ciphertext-record-data-is-equal (cdr a) (cdr b)))))

; snarkVM circuit/program/src/data/record/equal.rs: Record::is_equal (Ciphertext).
(define crypto-ciphertext-record-is-equal ((a crypto-ciphertext-recordp)
                                           (b crypto-ciphertext-recordp))
  :returns (r bitp)
  (b* ((da (crypto-ciphertext-record->data a))
       (db (crypto-ciphertext-record->data b))
       ((unless (equal (len da) (len db))) 0))
    (crypto-bit-and
     (crypto-bit-and
      (crypto-bit-and (crypto-ciphertext-owner-is-equal
                       (crypto-ciphertext-record->owner a)
                       (crypto-ciphertext-record->owner b))
                      (crypto-ciphertext-record-data-is-equal da db))
      (crypto-bit-eq (crypto-ciphertext-record->nonce a)
                     (crypto-ciphertext-record->nonce b)))
     (crypto-bit-eq (crypto-ciphertext-record->version a)
                    (crypto-ciphertext-record->version b)))))

; snarkVM circuit/program/src/data/record/equal.rs: Record::is_not_equal (Ciphertext).
(define crypto-ciphertext-record-is-not-equal ((a crypto-ciphertext-recordp)
                                               (b crypto-ciphertext-recordp))
  :returns (r bitp)
  (crypto-bit-not (crypto-ciphertext-record-is-equal a b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Record find.

; The identifier "owner" (Identifier::from_str: little-endian bytes, size 5).
(define crypto-owner-identifier ()
  :returns (id identifierp)
  (identifier (+ (char-code #\o)
                 (* (char-code #\w) (expt 256 1))
                 (* (char-code #\n) (expt 256 2))
                 (* (char-code #\e) (expt 256 3))
                 (* (char-code #\r) (expt 256 4)))
              5))

; IndexMap::get on the record data (the first entry with the name).
(define crypto-record-entry-lookup ((name identifierp) (data record-entry-listp))
  :returns (e (implies (not (reserrp e)) (entryp e)))
  (b* (((when (endp data)) (spec-error)))
    (if (equal (record-entry->name (car data)) (identifier-fix name))
        (record-entry->entry (car data))
      (crypto-record-entry-lookup name (cdr data)))))

; snarkVM circuit/program/src/data/record/entry/find.rs: Entry::find
; (Plaintext::find on the plaintext, keeping the visibility).
(define crypto-entry-find ((e entryp) (path access-listp))
  :returns (e1 (implies (not (reserrp e1)) (entryp e1)))
  (entry-case e
    :constant (b* (((fty::ok p) (crypto-plaintext-find e.get path))) (entry-constant p))
    :public (b* (((fty::ok p) (crypto-plaintext-find e.get path))) (entry-public p))
    :private (b* (((fty::ok p) (crypto-plaintext-find e.get path))) (entry-private p)))
  :verify-guards nil)

; snarkVM circuit/program/src/data/record/find.rs: Record::find.
; The path [owner] gives the owner as an entry; otherwise the first access
; must be a member naming an entry, and the rest of the path is followed
; in that entry.  An empty path or an index first access fails.
(define crypto-record-find ((r recordp) (path access-listp))
  :returns (e (implies (not (reserrp e)) (entryp e)))
  (b* (((when (and (equal (len path) 1)
                   (equal (acl2::access-fix (car path))
                          (acl2::access-member (crypto-owner-identifier)))))
        (crypto-owner-to-entry (record->owner r)))
       ((when (endp path)) (spec-error))
       (first (car path))
       ((unless (acl2::access-case first :member)) (spec-error))
       ((fty::ok entry) (crypto-record-entry-lookup (acl2::access-member->name first)
                                               (record->data r))))
    (if (endp (cdr path))
        entry
      (crypto-entry-find entry (cdr path))))
  :verify-guards nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Record encryption.

(define crypto-record-entry-names ((data record-entry-listp))
  :returns (names identifier-listp)
  (if (endp data)
      nil
    (cons (record-entry->name (car data))
          (crypto-record-entry-names (cdr data)))))

(define crypto-ciphertext-record-entry-names ((data crypto-ciphertext-record-entry-listp))
  :returns (names identifier-listp)
  (if (endp data)
      nil
    (cons (crypto-ciphertext-record-entry->name (car data))
          (crypto-ciphertext-record-entry-names (cdr data)))))

; The randomizers[index..index + k] slice (halts if out of range).
(define crypto-randomizer-slice ((randomizers values-field-listp) (index natp) (k natp))
  :returns (rs (implies (not (reserrp rs)) (values-field-listp rs)))
  (b* (((when (> (+ (lnfix index) (lnfix k)) (len randomizers))) (spec-error))
       (rest (nthcdr index (values-field-list-fix randomizers)))
       ((unless (<= (lnfix k) (len rest))) (spec-error)))
    (take k rest)))

(define crypto-record-encrypt-entries ((data record-entry-listp)
                                       (randomizers values-field-listp)
                                       (index natp))
  :returns (cdata (implies (not (reserrp cdata)) (crypto-ciphertext-record-entry-listp cdata)))
  (b* (((when (endp data)) nil)
       (name (record-entry->name (car data)))
       (entry (record-entry->entry (car data)))
       ((fty::ok k) (crypto-entry-num-randomizers entry))
       (k (nfix k))
       ((fty::ok rs) (crypto-randomizer-slice randomizers index k))
       ((fty::ok centry)
        (entry-case entry
          :constant (crypto-ciphertext-entry-constant entry.get)
          :public (crypto-ciphertext-entry-public entry.get)
          :private (b* (((fty::ok c) (crypto-plaintext-encrypt-with-randomizers
                                 entry.get rs)))
                     (crypto-ciphertext-entry-private c))))
       ((fty::ok rest) (crypto-record-encrypt-entries (cdr data) randomizers
                                                 (+ (lnfix index) k))))
    (cons (crypto-ciphertext-record-entry name centry) rest)))

; snarkVM circuit/program/src/data/record/encrypt.rs: Record::encrypt_with_randomizers.
; The owner takes randomizers[0] if private; each entry takes the next
; num_randomizers randomizers; duplicate entry names halt.
(define crypto-record-encrypt-with-randomizers ((r recordp)
                                                (randomizers values-field-listp))
  :returns (c crypto-ciphertext-record-resultp)
  (b* ((owner (record->owner r))
       ((fty::ok cowner)
        (if (owner-case owner :public)
            (crypto-owner-encrypt owner nil)
          (if (consp randomizers)
              (crypto-owner-encrypt owner (list (car randomizers)))
            (spec-error))))
       (index (if (owner-case owner :private) 1 0))
       ((fty::ok cdata) (crypto-record-encrypt-entries (record->data r) randomizers index))
       ((unless (no-duplicatesp-equal (crypto-record-entry-names (record->data r))))
        (spec-error)))
    (crypto-ciphertext-record cowner cdata (record->nonce r) (record->version r))))

; snarkVM circuit/program/src/data/record/encrypt.rs: Record::encrypt_symmetric_unchecked.
(define crypto-record-encrypt-symmetric-unchecked ((r recordp) (record-view-key fieldp))
  :returns (c crypto-ciphertext-record-resultp)
  (b* (((fty::ok n) (crypto-record-num-randomizers r))
       (n (nfix n))
       (randomizers (crypto-hash-many-psd
                     8 (list (crypto-encryption-domain) record-view-key) n)))
    (crypto-record-encrypt-with-randomizers r randomizers)))

; snarkVM circuit/program/src/data/record/encrypt.rs: Record::encrypt_symmetric.
; Asserts nonce = randomizer * G; the record view key is the x-coordinate of
; randomizer * owner.  Returns (list encrypted-record record-view-key).
(define crypto-record-encrypt-symmetric ((r recordp) (randomizer scalarp))
  :returns (res (implies (not (reserrp res))
                         (and (true-listp res)
                              (crypto-ciphertext-recordp (first res))
                              (fieldp (second res)))))
  (b* (((unless (equal (record->nonce r) (crypto-g-scalar-multiply randomizer)))
        (spec-error))
       (record-view-key
        (crypto-group-x (ecurve::edwards-bls12-mul
                         (lnfix randomizer)
                         (crypto-owner-address (record->owner r)))))
       ((fty::ok c) (crypto-record-encrypt-symmetric-unchecked r record-view-key)))
    (list c record-view-key)))

; snarkVM circuit/program/src/data/record/encrypt.rs: Record::encrypt.
(define crypto-record-encrypt ((r recordp) (randomizer scalarp))
  :returns (c (implies (not (reserrp c)) (crypto-ciphertext-recordp c)))
  (b* (((fty::ok res) (crypto-record-encrypt-symmetric r randomizer)))
    (crypto-ciphertext-record-fix (first res))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Record decryption.

(define crypto-record-decrypt-entries ((data crypto-ciphertext-record-entry-listp)
                                       (randomizers values-field-listp)
                                       (index natp))
  :returns (pdata (implies (not (reserrp pdata)) (record-entry-listp pdata)))
  (b* (((when (endp data)) nil)
       (name (crypto-ciphertext-record-entry->name (car data)))
       (entry (crypto-ciphertext-record-entry->entry (car data)))
       ((fty::ok k) (crypto-ciphertext-entry-num-randomizers entry))
       (k (nfix k))
       ((fty::ok rs) (crypto-randomizer-slice randomizers index k))
       ((fty::ok pentry)
        (crypto-ciphertext-entry-case entry
          :constant (entry-constant entry.get)
          :public (entry-public entry.get)
          :private (b* (((fty::ok p) (crypto-ciphertext-decrypt-with-randomizers
                                 entry.get rs)))
                     (entry-private p))))
       ((fty::ok rest) (crypto-record-decrypt-entries (cdr data) randomizers
                                                 (+ (lnfix index) k))))
    (cons (record-entry name pentry) rest)))

; snarkVM circuit/program/src/data/record/decrypt.rs: Record::decrypt_with_randomizers.
(define crypto-record-decrypt-with-randomizers ((c crypto-ciphertext-recordp)
                                                (randomizers values-field-listp))
  :returns (r record-resultp)
  (b* ((cowner (crypto-ciphertext-record->owner c))
       ((fty::ok owner)
        (if (crypto-ciphertext-owner-case cowner :public)
            (crypto-owner-decrypt cowner nil)
          (if (consp randomizers)
              (crypto-owner-decrypt cowner (list (car randomizers)))
            (spec-error))))
       (index (if (owner-case owner :private) 1 0))
       ((fty::ok pdata) (crypto-record-decrypt-entries (crypto-ciphertext-record->data c)
                                                  randomizers index))
       ((unless (no-duplicatesp-equal (crypto-ciphertext-record-entry-names
                                       (crypto-ciphertext-record->data c))))
        (spec-error)))
    (record owner pdata
            (crypto-ciphertext-record->nonce c)
            (crypto-ciphertext-record->version c))))

; snarkVM circuit/program/src/data/record/decrypt.rs: Record::decrypt_symmetric_unchecked.
(define crypto-record-decrypt-symmetric-unchecked ((c crypto-ciphertext-recordp)
                                                   (record-view-key fieldp))
  :returns (r record-resultp)
  (b* (((fty::ok n) (crypto-ciphertext-record-num-randomizers c))
       (n (nfix n))
       (randomizers (crypto-hash-many-psd
                     8 (list (crypto-encryption-domain) record-view-key) n)))
    (crypto-record-decrypt-with-randomizers c randomizers)))

; snarkVM circuit/program/src/data/record/decrypt.rs: Record::decrypt.
; The record view key is the x-coordinate of view_key * nonce; asserts that
; the view key's address (view_key * G) is the decrypted owner.
(define crypto-record-decrypt ((c crypto-ciphertext-recordp) (view-key scalarp))
  :returns (r record-resultp)
  (b* ((record-view-key
        (crypto-group-x (ecurve::edwards-bls12-mul
                         (lnfix view-key)
                         (crypto-ciphertext-record->nonce c))))
       ((fty::ok r) (crypto-record-decrypt-symmetric-unchecked c record-view-key))
       ((unless (equal (crypto-g-scalar-multiply view-key)
                       (crypto-owner-address (record->owner r))))
        (spec-error)))
    r))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Serial numbers, tags, and commitments.

; snarkVM circuit/program/src/data/record/serial_number.rs: Record::serial_number_from_gamma.
; sn_nonce = HashToScalarPSD2(sn_domain, (cofactor * gamma).x);
; serial number = CommitBHP512(sn_domain || commitment, sn_nonce).
(define crypto-record-serial-number-from-gamma ((gamma ecurve::edwards-bls12-pointp)
                                                (commitment fieldp))
  :returns (sn fieldp)
  (b* ((sn-nonce (crypto-hash-to-scalar-psd
                  2 (list (crypto-serial-number-domain)
                          (crypto-group-x (crypto-mul-by-cofactor gamma))))))
    (crypto-commit-bhp 512
                       (append (crypto-field-bits-le (crypto-serial-number-domain))
                               (crypto-field-bits-le commitment))
                       sn-nonce)))

; snarkVM circuit/program/src/data/record/serial_number.rs: Record::serial_number.
; gamma = sk_sig * HashToGroupPSD2(sn_domain, commitment); only sk_sig of the
; private key is used, so the private key is represented by sk_sig.
(define crypto-record-serial-number ((sk-sig scalarp) (commitment fieldp))
  :returns (sn (implies (not (reserrp sn)) (fieldp sn)))
  (b* (((fty::ok h) (crypto-hash-to-group-psd
                2 (list (crypto-serial-number-domain) commitment)))
       (gamma (ecurve::edwards-bls12-mul (lnfix sk-sig) h)))
    (crypto-record-serial-number-from-gamma gamma commitment)))

; snarkVM circuit/program/src/data/record/tag.rs: Record::tag = HashPSD2(sk_tag, commitment).
(define crypto-record-tag ((sk-tag fieldp) (commitment fieldp))
  :returns (tag fieldp)
  (crypto-hash-psd 2 (list sk-tag commitment)))

; snarkVM circuit/program/src/data/record/to_commitment.rs: Record::<Plaintext>::to_commitment.
; input = program_id || record_name || record bits; digest = HashBHP1024(input
; without its last 8 bits, the version); if the record is hiding (version != 0)
; the commitment is CommitBHP512(digest || version bits,
; HashToScalarPSD2(commitment_domain, record_view_key)), else the digest.
(define crypto-record-to-commitment ((r recordp)
                                     (program-id program-idp)
                                     (record-name identifierp)
                                     (record-view-key fieldp))
  :returns (cm (implies (not (reserrp cm)) (fieldp cm)))
  (b* (((fty::ok record-bits) (crypto-record-write-bits-le r))
       (input (append (crypto-program-id-bits-le program-id)
                      (crypto-identifier-bits-le record-name)
                      record-bits))
       (n (len input))
       ((when (< n 8)) (spec-error))
       (input-v0 (take (- n 8) input))
       (digest (crypto-hash-bhp 1024 input-v0))
       (input-v1 (append (crypto-field-bits-le digest)
                         (nthcdr (- n 8) input)))
       (cm-nonce (crypto-hash-to-scalar-psd
                  2 (list (crypto-commitment-domain) record-view-key)))
       (commitment (crypto-commit-bhp 512 input-v1 cm-nonce)))
    (if (equal (crypto-record-is-hiding (record->version r)) 0)
        digest
      commitment)))

; snarkVM circuit/program/src/data/record/to_commitment.rs: Record::<Ciphertext>::to_commitment
; (always halts: illegal on the ciphertext variant).
(define crypto-ciphertext-record-to-commitment ((r crypto-ciphertext-recordp)
                                                (program-id program-idp)
                                                (record-name identifierp)
                                                (record-view-key fieldp))
  (declare (ignore r program-id record-name record-view-key))
  :returns (cm reserrp)
  (spec-error))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Values to fields (used by requests and responses).

; snarkVM circuit/program/src/data/value/to_fields.rs: Value::to_fields.
(define crypto-value-to-fields ((v valuep))
  :returns (fields (implies (not (reserrp fields)) (values-field-listp fields)))
  (value-case v
    :plaintext (crypto-plaintext-to-fields v.get)
    :record (crypto-record-to-fields v.get)
    :future (crypto-bits-to-fields-checked (crypto-future-bits-le v.get))
    :dynamic-record (crypto-bits-to-fields-checked
                     (crypto-dynamic-record-bits-le v.get))
    :dynamic-future (crypto-bits-to-fields-checked
                     (crypto-dynamic-future-bits-le v.get))))
