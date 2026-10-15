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

The signature arm's hash stays abstract. `literal-signature-new-sound` takes that equality as a hypothesis:

- **Abstract hashes inside callers.** `Signature::new` (and therefore the signature arm of `Literal::new`) calls `hash_to_scalar_psd4` on the two x-coordinates. The circuit books use the abstract `values-hash-to-scalar-psd4` equality for that call. The Poseidon constraints are not expanded.
