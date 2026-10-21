# Charon + Aeneas extraction of the snarkVM circuits

`src/circuits.rs` restates the constraint-emitting code of snarkVM's
environment, Boolean, Field, Integer and Scalar circuits in the subset of Rust
that the Aeneas ACL2 backend accepts: no `Environment` trait, closures, slices,
or tuples wider than two. Each circuit appends R1CS constraints to a `Cs`
value. The `h_*` harnesses allocate input wires and run one circuit.

`circuits.lisp` is the book Aeneas writes for `src/circuits.rs`. The
`check-*.lisp` books run each harness and compare its constraints with the
gadget from `../r1cs` or `../fun-circuits` that the formalisation proves sound
and complete:

- `same-circuit` compares constraints in canonical form.
- `same-circuit-unordered` also ignores constraint order.
- `same-circuit-renamed` also renames internal wires, which it pairs by first
  occurrence.

The checks are in `check-boolean`, `check-field`, `check-integer`,
`check-integer-pow`, `check-scalar`, `check-group`, `check-address` and
`check-account`, `check-program`, `check-program-data`, `check-poseidon` and
`check-keccak`. Integer checks run at 8, 16, 32, 64 and 128 bits. A `*-differs` check records
a circuit that does not match its gadget.

The model stores constants as `i128 * 2^sh` without reducing them mod p, so it
cannot fold 253-bit constants. BHP, Pedersen and Elligator2 (253-bit bases) are
therefore `not-checked`, and Poseidon `hash_many` and `hash_to_scalar` are
checked with zero rounds (the permutation itself is checked with full rounds on
variable inputs). The environment sequence rows are proved over an abstract
element circuit, and the recursive Plaintext, Entry, Future, Argument, Record
and Value rows (and Literal `write_bits_*`) are over abstract leaf contracts,
so neither has a concrete gadget to compare.

`manifest.tsv` lists each row with STATUS `verified` in
`aleovm_circuit_function_formalisation_status.csv`, together with its check
and outcome. The outcome is one of `match`, `match-to-64`, `differs` or
`not-checked`. `StringType` is deprecated and will be removed from snarkVM,
so it has no rows and is not extracted; the `types/string` rows are
`IdentifierLiteral`.

`src/shape.rs` keeps snarkVM's trait, closure and `expect`. Charon accepts it,
but Aeneas rejects it because it cannot name the closure.

Regenerate and check with the pinned image
`ghcr.io/bendyarm/aeneas-acl2-dev:aeneas-23cf8c8_charon-58b7d54_acl2-0612757`
(Aeneas `23cf8c88`, Charon `58b7d543`, ACL2 `0612757b`):

```sh
books/projects/aleo/vm/circuits/aeneas-extraction/extract.sh
```

The script runs four checks:

- The regenerated book must match `circuits.lisp` byte for byte.
- `src/shape.rs` must still fail to extract.
- The check books must certify in the image. `rust-primitives.lisp` is copied
  from the image.
- `manifest.tsv` must cover exactly the verified rows and name only existing
  checks.
