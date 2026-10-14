; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Network functions that are not hash or commitment wrappers.
;
; Aleo*::enforce is in val-env-enforce.lisp (the enforce gadget, sample
; a=2, b=3, c=6).
;
; g_scalar_multiply folds Group::ternary(bit, output+base, output) over
; g_powers()[i] = 2^i G and the 251 little-endian scalar bits.  Group
; addition and ternary are types/group constraints and stay abstract.
; This book does not claim the fold equals edwards-bls12-mul; that link
; is the funspec's statement and is not proved from group gadgets here.
;
; verify_merkle_path_* calls MerklePath::verify.  The ordering constraint
; is merkle-path-verify-gadget (index bit 0 puts the running hash on the
; left).  curve-merkle-order now matches that order: indicator 1, which is
; the negation of an index bit of 0, returns (current, sibling).
; The one-level gadget is not yet proved equal to the whole
; aleo-verify-merkle-path-*-funspec, so those soundness and completeness
; flags stay 0.  See bugs-val.txt.

(in-package "ALEOVM")

(include-book "val-lib")
(include-book "val-collections")
(include-book "../fun-specs/curve-network")

(include-book "projects/pfcs/convenience-constructors" :dir :system)
(include-book "projects/pfcs/lifting" :dir :system)
(include-book "projects/pfcs/parser-interface" :dir :system)
(include-book "projects/pfcs/r1cs-subset" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled curve-merkle-order-matches-index-bit
  :short "Index bit 0 puts the running hash on the left, as in MerklePath::verify.
          The indicator passed to curve-merkle-order is the negation of that bit."
  (implies (bitp bit)
           (equal (mv-nth 0 (curve-merkle-order (- 1 bit) 'current 'sibling))
                  (if (equal bit 0) 'current 'sibling)))
  :enable curve-merkle-order)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define aleo-g-scalar-multiply-gadget ()
  :returns (constrs r1cs::r1cs-constraint-listp)
  :short "No constraints beyond abstract Group::add and Group::ternary."
  nil)

(defconst *aleo-g-scalar-multiply-sample* nil)

(defruled aleo-g-scalar-multiply-sample-holds
  (r1cs::r1cs-constraints-holdp (aleo-g-scalar-multiply-gadget)
                                *aleo-g-scalar-multiply-sample*
                                (base-prime))
  :enable (aleo-g-scalar-multiply-gadget r1cs::r1cs-constraints-holdp))

(defmacro val-g-scalar-bundle (name pfcs-name)
  `(progn
     (define ,name ()
       :returns (constrs r1cs::r1cs-constraint-listp)
       (aleo-g-scalar-multiply-gadget))
     (defruled ,(intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-GADGET-SOUND")
                 name)
       (implies (and (scalarp s)
                     (equal p (base-prime))
                     (r1cs::r1cs-valuationp asg p)
                     (r1cs::r1cs-constraints-holdp (,name) asg p))
                (equal (aleo-g-scalar-multiply-funspec s)
                       (ecurve::edwards-bls12-mul (lnfix s) (curve-generator-g))))
       :enable (,name aleo-g-scalar-multiply-gadget aleo-g-scalar-multiply-funspec
                      r1cs::r1cs-constraints-holdp))
     (defruled ,(intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-GADGET-COMPLETE")
                 name)
       (implies (and (equal p (base-prime))
                     (r1cs::r1cs-valuationp asg p)
                     (scalarp s))
                (r1cs::r1cs-constraints-holdp (,name) asg p))
       :enable (,name aleo-g-scalar-multiply-gadget))
     (defconst ,(intern-in-package-of-symbol
                 (concatenate 'string "*" (symbol-name name) "-SAMPLE*")
                 name)
       *aleo-g-scalar-multiply-sample*)
     (defruled ,(intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-SAMPLE-HOLDS")
                 name)
       (r1cs::r1cs-constraints-holdp
        (,name)
        ,(intern-in-package-of-symbol
          (concatenate 'string "*" (symbol-name name) "-SAMPLE*")
          name)
        (base-prime))
       :enable (,name aleo-g-scalar-multiply-sample-holds))
     (define ,(intern-in-package-of-symbol
               (concatenate 'string (symbol-name name) "-CIRCUIT")
               name)
       ()
       :returns (pdef pfcs::definitionp)
       (pfcs::parse-def
        ,(concatenate 'string pfcs-name "() := {\n    }"))
       ///
       (more-returns
        (pdef pfcs::sr1cs-definitionp
              :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                                 pfcs::sr1cs-constraintp
                                                 pfcs::r1cs-constraintp
                                                 pfcs::r1cs-polynomialp
                                                 pfcs::r1cs-monomialp))))))
     (pfcs::lift (,(intern-in-package-of-symbol
                    (concatenate 'string (symbol-name name) "-CIRCUIT")
                    name))
                 :pred ,(intern-in-package-of-symbol
                         (concatenate 'string (symbol-name name) "-PRED")
                         name)
                 :prime prime)
     (defruled ,(intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-PRED-TO-FUNSPEC")
                 name)
       (implies (equal prime (base-prime))
                (equal (,(intern-in-package-of-symbol
                          (concatenate 'string (symbol-name name) "-PRED")
                          name)
                        prime)
                       t))
       :enable (,(intern-in-package-of-symbol
                  (concatenate 'string (symbol-name name) "-PRED")
                  name)))))

(val-g-scalar-bundle aleo-v0-g-scalar-multiply-gadget "aleo_v0_g_scalar_multiply")
(val-g-scalar-bundle aleo-canary-v0-g-scalar-multiply-gadget "aleo_canary_v0_g_scalar_multiply")
(val-g-scalar-bundle aleo-testnet-v0-g-scalar-multiply-gadget "aleo_testnet_v0_g_scalar_multiply")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; verify_merkle_path_bhp / _psd for the three networks share the Rust
; ordering gadget.  The bhp/psd distinction is which abstract hash the
; caller passes; the constraints of the path (order + is_equal) are the same.

(defmacro val-verify-bundle (name pfcs-name)
  `(progn
     (define ,name ((bit symbolp) (cur symbolp) (sib symbolp)
                    (left symbolp) (right symbolp)
                    (root symbolp) (m symbolp) (r symbolp)
                    (p primep))
       :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
       (merkle-path-verify-gadget bit cur sib left right root m r p))
     (defruled ,(intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-SOUND")
                 name)
       (implies (and (symbolp bit) (symbolp cur) (symbolp sib)
                     (symbolp left) (symbolp right)
                     (symbolp root) (symbolp m) (symbolp r)
                     (equal p (base-prime))
                     (r1cs::r1cs-valuationp asg p)
                     (r1cs::valuation-bindsp asg bit)
                     (r1cs::valuation-bindsp asg cur)
                     (r1cs::valuation-bindsp asg sib)
                     (r1cs::valuation-bindsp asg left)
                     (r1cs::valuation-bindsp asg right)
                     (r1cs::valuation-bindsp asg root)
                     (r1cs::valuation-bindsp asg 'hashed)
                     (r1cs::valuation-bindsp asg m)
                     (r1cs::valuation-bindsp asg r)
                     (bitp (lookup-equal bit asg))
                     (fieldp (lookup-equal cur asg))
                     (fieldp (lookup-equal sib asg))
                     (fieldp (lookup-equal left asg))
                     (fieldp (lookup-equal right asg))
                     (fieldp (lookup-equal root asg))
                     (fieldp (lookup-equal 'hashed asg))
                     (bitp (lookup-equal r asg))
                     (crypto-field-hasher-p ph)
                     (equal (lookup-equal 'hashed asg)
                            (crypto-merkle-hash-children
                             ph
                             (list (lookup-equal left asg)
                                   (lookup-equal right asg))))
                     (r1cs::r1cs-constraints-holdp
                      (,name bit cur sib left right root m r p)
                      asg p))
                (and (equal (lookup-equal left asg)
                            (if (equal (lookup-equal bit asg) 0)
                                (lookup-equal cur asg)
                              (lookup-equal sib asg)))
                     (equal (lookup-equal right asg)
                            (if (equal (lookup-equal bit asg) 0)
                                (lookup-equal sib asg)
                              (lookup-equal cur asg)))))
       :enable (,name merkle-path-verify-gadget-sound))
     (defruled ,(intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-COMPLETE")
                 name)
       (implies (and (symbolp bit) (symbolp cur) (symbolp sib)
                     (symbolp left) (symbolp right)
                     (symbolp root) (symbolp m) (symbolp r)
                     (equal p (base-prime))
                     (r1cs::r1cs-valuationp asg p)
                     (r1cs::valuation-bindsp asg bit)
                     (r1cs::valuation-bindsp asg cur)
                     (r1cs::valuation-bindsp asg sib)
                     (r1cs::valuation-bindsp asg left)
                     (r1cs::valuation-bindsp asg right)
                     (r1cs::valuation-bindsp asg root)
                     (r1cs::valuation-bindsp asg 'hashed)
                     (r1cs::valuation-bindsp asg m)
                     (r1cs::valuation-bindsp asg r)
                     (bitp (lookup-equal bit asg))
                     (fieldp (lookup-equal cur asg))
                     (fieldp (lookup-equal sib asg))
                     (equal (lookup-equal left asg)
                            (if (equal (lookup-equal bit asg) 0)
                                (lookup-equal cur asg)
                              (lookup-equal sib asg)))
                     (equal (lookup-equal right asg)
                            (if (equal (lookup-equal bit asg) 0)
                                (lookup-equal sib asg)
                              (lookup-equal cur asg)))
                     (fieldp (lookup-equal root asg))
                     (fieldp (lookup-equal 'hashed asg))
                     (equal (lookup-equal r asg)
                            (if (equal (lookup-equal root asg)
                                       (lookup-equal 'hashed asg))
                                0 1))
                     (equal (lookup-equal m asg)
                            (if (equal (lookup-equal root asg)
                                       (lookup-equal 'hashed asg))
                                0
                              (pfield::inv (pfield::sub (lookup-equal root asg)
                                                        (lookup-equal 'hashed asg)
                                                        p)
                                           p))))
                (r1cs::r1cs-constraints-holdp
                 (,name bit cur sib left right root m r p) asg p))
       :enable (,name merkle-path-verify-gadget-complete))
     (defconst ,(intern-in-package-of-symbol
                 (concatenate 'string "*" (symbol-name name) "-SAMPLE*")
                 name)
       *merkle-path-verify-sample*)
     (defruled ,(intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-SAMPLE-HOLDS")
                 name)
       (r1cs::r1cs-constraints-holdp
        (,name 'bit 'cur 'sib 'left 'right 'root 'm 'r (base-prime))
        ,(intern-in-package-of-symbol
          (concatenate 'string "*" (symbol-name name) "-SAMPLE*")
          name)
        (base-prime))
       :enable (,name merkle-path-verify-sample-holds))
     (define ,(intern-in-package-of-symbol
               (concatenate 'string (symbol-name name) "-CIRCUIT")
               name)
       ()
       :returns (pdef pfcs::definitionp)
       (pfcs::parse-def
        ,(concatenate 'string
                      pfcs-name
                      "(bit, cur, sib, left, right, root, hashed, m, r) := {
    (cur - sib) * (1 - bit) == (left - sib),
    (sib - cur) * (1 - bit) == (right - cur),
    (root - hashed) * (m) == (r),
    (root - hashed) * (1 - r) == (0)
    }"))
       ///
       (more-returns
        (pdef pfcs::sr1cs-definitionp
              :hints (("Goal" :in-theory (enable pfcs::sr1cs-definitionp
                                                 pfcs::sr1cs-constraintp
                                                 pfcs::r1cs-constraintp
                                                 pfcs::r1cs-polynomialp
                                                 pfcs::r1cs-monomialp))))))
     (pfcs::lift (,(intern-in-package-of-symbol
                    (concatenate 'string (symbol-name name) "-CIRCUIT")
                    name))
                 :pred ,(intern-in-package-of-symbol
                         (concatenate 'string (symbol-name name) "-PRED")
                         name)
                 :prime prime)
     (defruled ,(intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-PRED-TO-ORDER")
                 name)
       (implies (and (equal prime (base-prime))
                     (bitp bit)
                     (fieldp cur) (fieldp sib) (fieldp left) (fieldp right)
                     (fieldp root) (fieldp hashed) (bitp r)
                     (pfield::fep m prime)
                     (,(intern-in-package-of-symbol
                        (concatenate 'string (symbol-name name) "-PRED")
                        name)
                      bit cur sib left right root hashed m r prime))
                (and (equal left (if (equal bit 0) cur sib))
                     (equal right (if (equal bit 0) sib cur))))
       :enable (,(intern-in-package-of-symbol
                  (concatenate 'string (symbol-name name) "-PRED")
                  name)
                merkle-path-verify-pred-to-funspec))))

(val-verify-bundle aleo-v0-verify-merkle-path-bhp-gadget
                   "aleo_v0_verify_merkle_path_bhp")
(val-verify-bundle aleo-v0-verify-merkle-path-psd-gadget
                   "aleo_v0_verify_merkle_path_psd")
(val-verify-bundle aleo-canary-v0-verify-merkle-path-bhp-gadget
                   "aleo_canary_v0_verify_merkle_path_bhp")
(val-verify-bundle aleo-canary-v0-verify-merkle-path-psd-gadget
                   "aleo_canary_v0_verify_merkle_path_psd")
(val-verify-bundle aleo-testnet-v0-verify-merkle-path-bhp-gadget
                   "aleo_testnet_v0_verify_merkle_path_bhp")
(val-verify-bundle aleo-testnet-v0-verify-merkle-path-psd-gadget
                   "aleo_testnet_v0_verify_merkle_path_psd")
