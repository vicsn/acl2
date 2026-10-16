# FUN-SPEC books

Functional specifications of the constraint-generating functions in snarkVM's
circuit crates, written against snarkVM `7dc117d45` (2026-10-14). Each row of
`aleovm_circuit_function_formalisation_status.csv` (repository root) is mapped
to its spec in `aleovm_circuit_function_funspec_map.tsv`. `top.lisp` includes
all books.

## Known limitations

- **Hashes are abstract.** Poseidon, BHP, Pedersen, Keccak and Elligator2 are
  constrained functions in `base.lisp` with only their result types known. The
  25 algorithms-crate rows are excluded from FUN-SPEC. Elligator2 failure is
  modelled only for input 0 (`curve-elligator2-encode-validp` in
  `curve-network.lisp`).
- **Subgroup membership is not proved.** Group-valued results are proved to be
  curve points (`ecurve::edwards-bls12-pointp`), not points in the prime-order
  subgroup. `values-to-group` in `values-helpers.lisp` assumes it.
- **Two generators.** `curve-generator-g` (`curve-network.lisp`) is snarkVM's
  concrete G. The `crypto-*` books use the abstract `crypto-generator-g` and
  abstract commitment, encryption and serial-number domains
  (`crypto-model.lisp`). Nothing ties the two together.
- **Abstract serialization in `crypto-*`.** The bit encodings of plaintexts,
  futures, dynamic records and dynamic futures are abstract in
  `crypto-values.lisp`, not the `values-*` definitions. `crypto-state-path.lisp`
  has its own leaf representation.
- **Plaintext bit cache.** snarkVM's `Plaintext::from_bits_*` keeps the raw
  input bits, which later `write_bits_*` and `to_fields*` return. The specs
  recompute the bits instead, so they can differ for plaintexts built from bits
  (32 rows; see the notes in the map).
- **Not executable.** These are defined by quantifiers or `defchoose`:
  `group-from-x-coordinate-funspec`, `field-square-root-funspec`,
  `field-even-square-root-funspec` and `crypto-group-with-x`. The last one
  models `Address::from_field` and assumes, without proof, that the point with
  a given x-coordinate is unique.
- **Root order.** `field-square-roots-flagged-nondeterministic-funspec` returns
  the roots in snarkVM's order (smaller first). The constraints don't fix it.
- **Unverified guards** (logically defined, but not checked to be Common Lisp
  compliant):
  - `crypto-merkle-tree-new`, `crypto-kary-merkle-path-verify`
  - `crypto-record-find`, `crypto-entry-find`, `crypto-plaintext-find`
  - `crypto-request-check-input-ids`, `crypto-request-verify`
  - `crypto-response-from-outputs`,
    `crypto-response-process-outputs-from-callback` and the output-ID helpers
- **Not modelled.**
  - Variable modes, except for the `both-variable` flag of
    `field-div-unchecked-funspec`.
  - The requirement that `find` indices be constants.
  - snarkVM's constraint and density limits.
  - Console-only optional data of dynamic records and futures.

## Open TODOs

Remove an item only when a certified book discharges it.

`Literal::new` needs `books/projects/aleo/vm/snarkVM-scalar-new-range-check.patch`:

- **Scalar::new soundness finding.** At snarkVM `7dc117d45` a public or private `Scalar::new` is `Field::new` of the value and emits no constraint. The base field (about 2^253) is larger than the scalar field (about 2^251), so a witness in [r, p) satisfies the circuit without being a scalar. `scalar-new-unpatched-accepts-non-scalar` in `fun-circuits/scalar-new-r1cs.lisp` is that assignment. The patch makes a variable `Scalar::new` call `to_bits_le`, which emits 503 constraints: 251 boolean checks, the weighted-sum `assert_eq`, `assert_less_than_or_equal_constant` against r - 1, and the final assert. `scalar-new-gadget` is that list and `scalar-new-gadget-sound` proves the wire is a scalar. The same check applies to the two scalars of `Signature::new`. `aleovm_sample_circuits.py` fails on unpatched samples (0 and 873 constraints) and passes on patched ones (503 and 1879).

R1CS-SOUND is stated over the wires: from a satisfying assignment, the literal is built from the wire values, the theorem proves the type predicate of those values, and `literal-new` returns that literal. `literal-identifier-new-sound` in `fun-circuits/identifier-list-sound.lisp` is the identifier arm. The other arms are in `fun-circuits/literal-new-r1cs.lisp`. `fun-circuits/literal-new-pfcs.lisp` lowers the constraints snarkVM emits for this row to those R1CS gadgets: boolean checks, the empty field circuit, the patched scalar range check, the string size `assert_eq`, `enforce_in_group`, the identifier validation relations, and the signature composition. The scalar weighted sum and the string size relations are written by hand next to their PFCS definitions; they are not produced by `pfcs::lift`.

R1CS-SOUND for `Literal::new` stays 0 while this remains:

- **Cofactor clearing.** `group-enforce-in-group-sound` in `fun-circuits/group-inject-sound.lisp` proves that the `enforce_in_group` equations make the output 4Q for a curve point Q, with the doubling formulas proved equal to `edwards-bls12-add`. That 4Q is in the prime-order subgroup is the hypothesis `edwards-bls12-cofactor-clears` (for every curve point Q, 2Q + 2Q is an r-point). It needs the curve order, which is not formalised. The group, address, and signature arms of R1CS-SOUND take that hypothesis.

R1CS-COMPLETE for `Literal::new` stays 0 while any of these remains:

- **Subgroup witness.** `Group::new`, `Address::new`, and the group elements inside `ComputeKey::new` emit `enforce_in_group`: a private cofactor witness `Q`, `enforce_on_curve` on `Q`, `double`, and `enforce_double` against the input. It is not proved that every `groupp` point has a `Q` with `4Q = P`. R1CS-COMPLETE for any caller of `Group::new` stays open until that witness is constructed.
- **Scalar comparison witness.** Completeness of the patched `Scalar::new` needs the bit witnesses and the comparison-chain witnesses of `bits-lte-const-gadget` for every scalar. That construction is not done, so the scalar and signature arms have no R1CS-COMPLETE theorem.
- **Host halt versus unsatisfiable R1CS.** `StringType::new` halts when the byte length does not fit in `u32`, before emitting constraints. `string-type-new` returns `(spec-error)` in that case. The constraints that would have been emitted (a size `assert_eq` and the byte boolean checks) are satisfiable for that length, so the error is not an unsatisfiable R1CS. The same pattern applies to any other host halt. Do not mark R1CS-COMPLETE for a function whose only failure is a host halt.

R1CS-SOUND is over the wires. A theorem that takes `int-valuep`, `scalarp`, or `edwards-bls12-pointp` as a hypothesis, and assumes the wires are that value, is not unconditional. `R1CS-SOUND-IF` names a prior circuit that already established that hypothesis on the same value. The flag is 1 only together with that circuit. An empty cell is unconditional when the flag is 1, and means no sufficient prior circuit when the flag is 0. `Integer::new` and `Integer::from_field` build the integer from the bit wires. `Integer::from_field_lossy` does too when the public unit wire is 1. `enforce_on_curve` soundness takes `curve-coordinatesp`, and no unconditional circuit discharges that or `edwards-bls12-pointp`, so group and address flags stay 0. Its PFCS, `crv-group-enforce-on-curve-pred-to-funspec`, is certified.

`R1CS-SOUND-IF` is `Integer::new` on each integer input for compare, equality, `is_zero`, `is_one`, bitwise operations, checked and wrapped addition, and checked subtraction, including the assign forms. `abs_checked`, `abs_wrapped`, `to_field`, `to_fields`, and `to_scalar` name `Integer::new` on that one input. `neg` names `Integer::new` on a signed input: unsigned negation is a host halt and has no circuit. `ternary` also needs `Boolean::new` on the condition, because the ternary gadget does not boolean-check it. `from_bits_le` and `from_bits_be` name `Boolean::new` on each input bit: the theorem takes `bit-listp`, and the no-excess path adds no constraint. `Integer::from_field` establishes the same `int-valuep` and little-endian bits as `Integer::new`. `Integer::from_field_lossy` does so when its public unit wire is 1. The equality gadget still assumes its public unit wire is 1.

There is no `Scalar::new` row. Unpatched `Scalar::new` emits no constraint. `Scalar::to_bits_le` is the CSV row `write_bits_le`, and `scalar-write-bits-le-gadget-sound` proves that wire is a scalar. The same constraint list is the patched `Scalar::new`. Scalar compare, `is_equal`, `is_not_equal`, `is_zero`, and `is_one` therefore have `R1CS-SOUND-IF` equal to `Scalar::to_bits_le` on each operand (one operand for `is_zero` and `is_one`). Scalar `ternary` also needs `Boolean::new` on the condition. `Scalar::from_field` establishes `scalarp` of that same wire when its public unit wire is 1. Scalar comparison still assumes its own public unit wire is 1. The scalar arm of `Literal::new` is sound for a wire on which `Scalar::to_bits_le` already ran. That row stays 0: the group arm still needs cofactor clearing.

These stay 0 with an empty `R1CS-SOUND-IF`. The operation itself is not proved, or the missing hypothesis is not a circuit that is unconditionally sound: integer multiplication, exponentiation, shifts, wrapped subtraction, and division (unsigned soundness is only widths 8, 16, 32, and 64, and the dividend and divisor bits are unchecked); group addition, equality, ternary, bit output, and `is_zero`; address compare, equality, ternary, bit output, and `from`; `ComputeKey` and `Signature` equality, ternary, and `to_fields`; `to_non_unique_bits`; `square_roots_flagged_nondeterministic`; merkle paths; `g_scalar_multiply`; `OutputID::record`; `ProgramID::to_address`.

`Scalar::is_equal`, `is_zero`, and `is_one` are field equality on the embedding (`circuit/types/scalar/src/equal.rs`). `scalar-equal-modulus-disagrees-with-residue` in `fun-circuits/scalar-range-gap.lisp` is a satisfying assignment of those two enforces for the wires `r` and `0`: the not-equal bit is 1, so the `is_equal` linear combination is 0, while both residues are 0. `scalar-one-modulus-disagrees-with-residue` is the same gadget on `r+1` and `1`: the residue is 1 and the circuit returns 0. `Scalar::ternary` copies the field wire. `scalar-ternary-copies-non-scalar` is condition 1 copying `r`, and the output fails `scalarp`. `Scalar::is_less_than` returns the parity of `2*(self - other)` in the base field. `crv-scalar-less-than-parity-not-scalar-order` shows `2*(r - 1)` is even, so that bit is 0 for the wires `r` and `1`, while the residues are `0` and `1`. `Scalar::add` does reduce modulo `r`, so the wire `r` added to 0 is the scalar 0 while `is_equal` of those wires is false.

`Scalar::from_field_lossy` is `Field::to_bits_le` and then the low 250 bits (`fun-circuits/scalar-from-field-lossy-r1cs.lisp`). `scalar-from-field-lossy-gadget-sound` builds that scalar from the bit wires and proves `scalarp`. `zero-unit-gadget` does not force the unit wire, so the theorem takes `(lookup-equal u asg) = 1`, the public one. PFCS and R1CS-COMPLETE stay open: the bits-below-prime witness is not constructed.

`Integer::from_field_lossy` is the same `Field::to_bits_le` circuit, sliced to the integer width (`fun-circuits/int-from-field-lossy-sound.lisp`). `int-from-field-lossy-sound-gadget-sound` reads the integer with `lebits->int` of the first `n` bit wires and proves `int-valuep` for either signedness. The unit wire is again the public one. PFCS and R1CS-COMPLETE stay open for the same missing bits-below-prime witness.

`Scalar::write_bits_le` is the same constraint list as the patched `Scalar::new` (`fun-circuits/scalar-write-bits-r1cs.lisp`). `scalar-write-bits-le-gadget-sound` proves the bit wires are `scalar-bits-le` of a scalar. `write_bits_be` reverses that list and emits nothing further. The funspec prefix is an unconstrained accumulator, assumed to be a bit list. PFCS and R1CS-COMPLETE stay open: the `bits-lte-const` witness is not constructed for every scalar.

`Scalar::from_field` is `Scalar::from_bits_le` of `Field::to_bits_le` (`fun-circuits/scalar-from-bits-r1cs.lisp`). `scalar-from-field-gadget-sound` proves the two excess bits are 0, the low 251 bits are at most `r - 1`, and that value is a scalar equal to `scalar-from-field-funspec`. The unit wire is the public one. `scalar-from-field-pfcs-iff-r1cs` lowers that constraint list to the boolean checks, the power-of-two sum, the field range chain, the unit check, the excess sum, the scalar range chain, and the final assert. `scalar-from-field-gadget-complete` is the success direction for the canonical field bits and both fold witnesses.

`Scalar::from_bits_le` boolean-checks nothing (`fun-circuits/scalar-from-bits-r1cs.lisp`). Past 250 bits it emits `assert_bits_are_zero` on the excess, `bits-lte-const` against `r - 1`, and the final assert. At most 250 bits emits nothing. `scalar-from-bits-le-gadget-implies-funspec` proves the funspec and `scalarp` under `bit-listp`, so R1CS-SOUND is 1 only with `R1CS-SOUND-IF` equal to `Boolean::new` on each input bit. `scalar-from-bits-le-gadget-complete` builds the fold witness for every bit list whose funspec returns a value. `scalar-from-bits-le-pfcs-iff-r1cs` is only the longer-than-250 case, so PFCS-SPEC stays 0. `from_bits_be` reverses and emits nothing further.

Unsigned integer division at widths 8, 16, 32, and 64 (`fun-circuits/int-div-pfcs.lisp`) lowers `INT_UNSIGNED_DIV_n` to `unsigned-small-div-gadget`. That is the constraint list of `div`, `div_assign`, `div_checked`, `div_wrapped`, `rem`, `rem_assign`, `rem_checked`, `rem_wrapped`, `modulo`, and `unsigned_division_via_witness`. Quotient and remainder bits are boolean-checked. Dividend and divisor bits are not, so R1CS-SOUND stays 0. Signed division and width 128 are different circuits. R1CS-COMPLETE is open.

Integer shifts (`fun-circuits/int-shift-pfcs.lisp`) lift only the exponent-bit-0 doubling select, `int-shift-step-pred-to-after`. Later exponent bits are `int-shift-var-step-gadget` with coefficient `2^(2^i)-1`, not a lifted PFCS, so none of the eight shift rows gain PFCS-SPEC from this book. Value bits and exponent bits are not boolean-checked, so R1CS-SOUND stays 0. `int-shl-wrapped-gadget-complete` is variable-mode completeness for both signednesses at every width other than 128. Width 128 is a different circuit, and a constant exponent emits no select, so that row's R1CS-COMPLETE stays 0. Checked left shift has a success witness only when the exponent is below the width and the product fits, and unsatisfiability only when the exponent magnitude is 8, 16, or 32 and the exponent is at least the width. The overflow error is not proved unsatisfiable. Signed checked shifts and right-shift value witnesses are not this proof.

`ComputeKey::from_private_key` (`fun-circuits/compute-key-from-private-key.lisp`) is two `Aleo::g_scalar_multiply` calls and `hash_to_scalar_psd4` of the two x coordinates. `g-scalar-window` is the 251-step fold `Group::ternary(bit, acc + 2^i G, acc)` from `Group::zero()`. `g-scalar-window-of-scalar-from-zero` equates that fold on `scalar-bits-le` to `edwards-bls12-mul` under `twisted-edwards-add-associativity`. `compute-key-from-private-key-is-scalar-windows` is both folds, then `compute-key-from-funspec`. Variable mode emits 4353 constraints: two `Scalar::to_bits_le` (503 each), two 250-step folds (a variable/constant `Group::add` is 3 constraints and the following `Group::ternary` is 2; the first step adds constant zero to constant `G` and emits nothing), and `hash_to_scalar_psd4` of two fields (847). The variable/variable addition gadget is a different circuit, and Poseidon stays abstract, so R1CS-SPEC, PFCS-SPEC, R1CS-SOUND, and R1CS-COMPLETE stay 0. Associativity is not a prior circuit, so `R1CS-SOUND-IF` stays empty. The same fold lemma is why `g_scalar_multiply` no longer says the fold is unproved; its gadget is still empty, so that row's soundness stays 0.

ACL2 `defruled` samples, including prime-5 write-bits and scalar-comparison assignments, are not `R1CS-SAMPLES`. That flag requires `aleovm_sample_circuits.py` against a snarkVM scope dump.

The signature arm's hash stays abstract. `literal-signature-new-sound` takes that equality as a hypothesis:

- **Abstract hashes inside callers.** `Signature::new` (and therefore the signature arm of `Literal::new`) calls `hash_to_scalar_psd4` on the two x-coordinates. The circuit books use the abstract `values-hash-to-scalar-psd4` equality for that call. The Poseidon constraints are not expanded.
