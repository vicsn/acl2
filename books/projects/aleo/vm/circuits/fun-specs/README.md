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
