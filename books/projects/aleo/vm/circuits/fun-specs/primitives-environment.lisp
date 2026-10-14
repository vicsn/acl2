; AleoVM Library
;
; Copyright (C) 2026 Provable Inc.
;
; License: See the LICENSE file distributed with this library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Functional specifications of the constraint-generating functions
; of snarkVM's circuit/environment crate.
;
; Conventions specific to the primitives-* books:
;   - Spec names end in -funspec, to avoid clashing with the
;     pfcs/ and r1cs/ books, which use -spec names in the same package.
;   - Functions that return () in Rust and only add constraints
;     (enforce, assert, assert_eq, ...) are specified as predicates:
;     the predicate holds iff snarkVM neither halts nor generates
;     unsatisfiable constraints, i.e. it is false exactly in the error case.
;   - Linear combinations are specified by their values (field elements).
;   - Resource limits of the environment (constraint/density limits,
;     witness mode) are not modeled.

(in-package "ALEOVM")

(include-book "base")

(local (in-theory (enable spec-error fieldp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Modes

(define modep (x)
  :returns (yes/no booleanp)
  :short "Variable modes of snarkVM circuits."
  (and (member-eq x '(:constant :public :private)) t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Constraints and assertions

; snarkVM circuit/environment/src/circuit.rs, canary_circuit.rs, testnet_circuit.rs: Environment::enforce
(define enforce-funspec ((a fieldp) (b fieldp) (c fieldp))
  :returns (yes/no booleanp)
  :short "@('E::enforce(|| (A, B, C))'): the R1CS relation @($A \\cdot B = C$)
          holds on the values of the linear combinations."
  :long "If all three are constants and the relation fails, snarkVM returns
         @('Err(ConstraintUnsatisfied)'); otherwise an unsatisfiable constraint
         is added. Both are errors."
  (equal (pfield::mul a b (base-prime)) c))

; snarkVM circuit/environment/src/environment.rs: Environment::assert
(define assert-funspec ((b fieldp))
  :returns (yes/no booleanp)
  :short "@('E::assert(b)') enforces @($b \\cdot 1 = 1$)."
  (enforce-funspec b 1 1)
  :guard-hints (("Goal" :in-theory (enable fieldp pfield::fep))))

; snarkVM circuit/environment/src/environment.rs: Environment::assert_eq
(define assert-eq-funspec ((a fieldp) (b fieldp))
  :returns (yes/no booleanp)
  :short "@('E::assert_eq(a, b)') enforces @($a \\cdot 1 = b$)."
  (enforce-funspec a 1 b)
  :guard-hints (("Goal" :in-theory (enable fieldp pfield::fep))))

; snarkVM circuit/environment/src/environment.rs: Environment::assert_neq
(define assert-neq-funspec ((a fieldp) (b fieldp))
  :returns (yes/no booleanp)
  :short "@('E::assert_neq(a, b)') enforces @($(a - b) \\cdot m = 1$),
          where the multiplier @($m$) is @($(a - b)^{-1}$), or 0 if @($a = b$)."
  (b* ((p (base-prime))
       (a-minus-b (pfield::sub a b p))
       (multiplier (if (equal a-minus-b 0) 0 (pfield::inv a-minus-b p))))
    (enforce-funspec a-minus-b multiplier 1))
  :guard-hints (("Goal" :in-theory (enable fieldp pfield::fep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Generic ToBits / ToBitsRaw

; The type-specific write_bits_* functions (e.g. of Field, Scalar)
; are abstracted by constrained functions: a write function extends the
; accumulator with the bits of the circuit. The element types of
; Vec, slices, arrays and tuples are generic in snarkVM.

(encapsulate
  (((write-bits-le-impl * *) => * :formals (acc x) :guard t)
   ((write-bits-be-impl * *) => * :formals (acc x) :guard t)
   ((write-bits-raw-le-impl * *) => * :formals (acc x) :guard t)
   ((write-bits-raw-be-impl * *) => * :formals (acc x) :guard t))

  (local (defun write-bits-le-impl (acc x)
           (declare (ignore x))
           (true-list-fix acc)))
  (local (defun write-bits-be-impl (acc x)
           (declare (ignore x))
           (true-list-fix acc)))
  (local (defun write-bits-raw-le-impl (acc x)
           (declare (ignore x))
           (true-list-fix acc)))
  (local (defun write-bits-raw-be-impl (acc x)
           (declare (ignore x))
           (true-list-fix acc)))

  (local (defrule bit-listp-of-true-list-fix
           (implies (bit-listp x)
                    (bit-listp (true-list-fix x)))))

  (defrule bit-listp-of-write-bits-le-impl
    (implies (bit-listp acc)
             (bit-listp (write-bits-le-impl acc x))))
  (defrule bit-listp-of-write-bits-be-impl
    (implies (bit-listp acc)
             (bit-listp (write-bits-be-impl acc x))))
  (defrule bit-listp-of-write-bits-raw-le-impl
    (implies (bit-listp acc)
             (bit-listp (write-bits-raw-le-impl acc x))))
  (defrule bit-listp-of-write-bits-raw-be-impl
    (implies (bit-listp acc)
             (bit-listp (write-bits-raw-be-impl acc x))))

  (defruled write-bits-le-impl-extends-accumulator
    (equal (write-bits-le-impl acc x)
           (append acc (write-bits-le-impl nil x))))
  (defruled write-bits-be-impl-extends-accumulator
    (equal (write-bits-be-impl acc x)
           (append acc (write-bits-be-impl nil x))))
  (defruled write-bits-raw-le-impl-extends-accumulator
    (equal (write-bits-raw-le-impl acc x)
           (append acc (write-bits-raw-le-impl nil x))))
  (defruled write-bits-raw-be-impl-extends-accumulator
    (equal (write-bits-raw-be-impl acc x)
           (append acc (write-bits-raw-be-impl nil x)))))

; snarkVM circuit/environment/src/traits/to_bits.rs: ToBits::to_bits_le (trait default)
(define to-bits-le-funspec (x)
  :short "@('to_bits_le') writes the little-endian bits into an empty vector."
  (write-bits-le-impl nil x))

; snarkVM circuit/environment/src/traits/to_bits.rs: ToBits::to_bits_be (trait default)
(define to-bits-be-funspec (x)
  :short "@('to_bits_be') writes the big-endian bits into an empty vector."
  (write-bits-be-impl nil x))

; snarkVM circuit/environment/src/traits/to_bits.rs: ToBitsRaw::to_bits_raw_le (trait default)
(define to-bits-raw-le-funspec (x)
  :short "@('to_bits_raw_le') writes the raw little-endian bits into an empty vector."
  (write-bits-raw-le-impl nil x))

; snarkVM circuit/environment/src/traits/to_bits.rs: ToBitsRaw::to_bits_raw_be (trait default)
(define to-bits-raw-be-funspec (x)
  :short "@('to_bits_raw_be') writes the raw big-endian bits into an empty vector."
  (write-bits-raw-be-impl nil x))

; snarkVM circuit/environment/src/traits/to_bits.rs: ToBits::write_bits_le for Vec<C>, [C; N], &[C], tuples
(define write-bits-le-seq-funspec (acc (elems true-listp))
  :short "Write the little-endian bits of each element in order,
          i.e. concatenate the element bits (no overall reversal)."
  (if (endp elems)
      acc
    (write-bits-le-seq-funspec (write-bits-le-impl acc (car elems))
                               (cdr elems))))

; snarkVM circuit/environment/src/traits/to_bits.rs: ToBits::write_bits_be for Vec<C>, [C; N], &[C], tuples
(define write-bits-be-seq-funspec (acc (elems true-listp))
  :short "Write the big-endian bits of each element in order,
          i.e. concatenate the element bits (no overall reversal)."
  (if (endp elems)
      acc
    (write-bits-be-seq-funspec (write-bits-be-impl acc (car elems))
                               (cdr elems))))

; snarkVM circuit/environment/src/traits/to_bits.rs: ToBitsRaw::write_bits_raw_le for Vec<C>, [C; N], &[C], tuples
(define write-bits-raw-le-seq-funspec (acc (elems true-listp))
  :short "Write the raw little-endian bits of each element in order."
  (if (endp elems)
      acc
    (write-bits-raw-le-seq-funspec (write-bits-raw-le-impl acc (car elems))
                                   (cdr elems))))

; snarkVM circuit/environment/src/traits/to_bits.rs: ToBitsRaw::write_bits_raw_be for Vec<C>, [C; N], &[C], tuples
(define write-bits-raw-be-seq-funspec (acc (elems true-listp))
  :short "Write the raw big-endian bits of each element in order."
  (if (endp elems)
      acc
    (write-bits-raw-be-seq-funspec (write-bits-raw-be-impl acc (car elems))
                                   (cdr elems))))

(defrule bit-listp-of-write-bits-le-seq-funspec
  (implies (bit-listp acc)
           (bit-listp (write-bits-le-seq-funspec acc elems)))
  :enable write-bits-le-seq-funspec)

(defrule bit-listp-of-write-bits-be-seq-funspec
  (implies (bit-listp acc)
           (bit-listp (write-bits-be-seq-funspec acc elems)))
  :enable write-bits-be-seq-funspec)

(defrule bit-listp-of-write-bits-raw-le-seq-funspec
  (implies (bit-listp acc)
           (bit-listp (write-bits-raw-le-seq-funspec acc elems)))
  :enable write-bits-raw-le-seq-funspec)

(defrule bit-listp-of-write-bits-raw-be-seq-funspec
  (implies (bit-listp acc)
           (bit-listp (write-bits-raw-be-seq-funspec acc elems)))
  :enable write-bits-raw-be-seq-funspec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Generic Inject

; The type-specific Inject::new functions are abstracted by a
; constrained function, returning the injected value or an error.

(encapsulate
  (((inject-impl * *) => * :formals (mode value) :guard t))
  (local (defun inject-impl (mode value)
           (declare (ignore mode))
           value)))

; snarkVM circuit/environment/src/traits/inject.rs: Inject::new for Vec<C> and tuples
(define inject-seq-funspec ((mode modep) (values true-listp))
  :short "Inject each component with the same mode;
          error if any component injection errors."
  (b* (((when (endp values)) nil)
       (first (inject-impl mode (car values)))
       ((when (reserrp first)) (spec-error))
       (rest (inject-seq-funspec mode (cdr values)))
       ((when (reserrp rest)) (spec-error)))
    (cons first rest)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The witness! macro helpers (proc-macro on token streams)

; A token tree is modeled as:
;   (:ident . name)            an identifier, with name a string;
;   (:group delimiter . stream) a delimited group of token trees;
;   anything else              a punctuation or literal token.

; snarkVM circuit/environment/witness/src/lib.rs: recursively_replace_self
(define recursively-replace-self-funspec (stream (replacement stringp))
  :short "Replace every identifier @('self') by @('replacement'),
          recursively inside groups, leaving other tokens unchanged."
  :measure (acl2-count stream)
  :returns (new-stream true-listp)
  (b* (((when (atom stream)) nil)
       (tok (car stream))
       (new-tok
        (cond ((and (consp tok) (eq (car tok) :ident))
               (if (equal (cdr tok) "self")
                   (cons :ident replacement)
                 tok))
              ((and (consp tok) (eq (car tok) :group) (consp (cdr tok)))
               (list* :group
                      (cadr tok)
                      (recursively-replace-self-funspec (cddr tok)
                                                        replacement)))
              (t tok))))
    (cons new-tok
          (recursively-replace-self-funspec (cdr stream) replacement))))

; snarkVM circuit/environment/witness/src/lib.rs: rename_selfs
(define rename-selfs-funspec (stream)
  :returns (new-stream true-listp)
  :short "The @('rename_selfs!') proc-macro renames @('self') to @('_self')."
  (recursively-replace-self-funspec stream "_self"))
