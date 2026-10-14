# AleoVM circuit formalisation

Circuit work is recorded in two places that must move together:

- `aleovm_circuit_function_formalisation_status.csv` at the repository root
- `books/projects/aleo/vm/circuits/fun-specs/README.md`

## Status table

Do not hand-edit flag columns in the CSV. `aleovm_circuit_functions_scan.py` regenerates the file from the snarkVM `circuit/` tree, from `ACL2_MODELS`, from `aleovm_circuit_function_funspec_map.tsv` (FUN-SPEC only), and from `aleovm_circuit_function_circspec_map.tsv` (the five circuit flags).

```
python3 aleovm_circuit_functions_scan.py <snarkVM>/circuit aleovm_circuit_function_formalisation_status.csv
```

The root argument must be the `circuit/` directory so paths look like `circuit/...`. The tree is snarkVM commit `7dc117d45` (2026-10-14), not the 2023 submodule under `books/projects/aleo/vm/snarkVM`.

When a circuit task is finished:

- Add a row to `aleovm_circuit_function_circspec_map.tsv`. A column value `1` sets that flag. A `0` does not clear a `1` already recorded from `ACL2_MODELS` or from an earlier map row.
- Do not clear an existing `1`.
- Leave rows whose FUN-SPEC is `excluded` (the hash and algorithm internals) unchanged.
- Set a flag to `1` only after `books/build/cert.pl` has accepted the book named in the `acl2` column.
- Regenerate the CSV in the same change as the book.

The columns mean:

- **R1CS-SPEC / PFCS-SPEC.** The formal constraints are the ones snarkVM emits. A fully constant triple is checked by the host and is not a constraint. Boolean NOT and field addition are linear combinations; do not add a constraint for them. A PFCS definition that lowers to that R1CS discharges both columns.
- **R1CS-SAMPLES.** `python3 aleovm_sample_circuits.py --snarkvm <snarkVM>` rebuilds the scope dumps and checks their shapes. The sampler lives on `github.com/vicsn/snarkVM` branch `aleovm-scope-samples` and in `books/projects/aleo/vm/snarkVM-sample.patch` (plus `snarkVM-literal-new-sample.patch`).
- **R1CS-SOUND.** Every satisfying assignment of the formal circuit has I/O that matches the funspec.
- **R1CS-COMPLETE.** Every funspec input that returns a value has a satisfying assignment, and an input on which the funspec returns `(spec-error)` has none.

Higher-level gadgets call the lower-level ones (`boolean-check-gadget`, `boolean-check-gadget-list`, `enforce-gadget`, `assert-eq-gadget`, `assert-gadget`, and the gadgets under `fun-circuits/`) instead of restating them.

## Fun-spec README

`books/projects/aleo/vm/circuits/fun-specs/README.md` is the list of open limitations. When a proof stops short of a flag, add the gap there in the same change, under **Open TODOs**. In particular:

- Poseidon, BHP, Pedersen, Keccak, and Elligator2 stay abstract. A caller that emits one of those circuits (for example `Signature::new` via `hash_to_scalar_psd4`) uses the abstract funspec equality for that call. Say so in the README; do not invent a stand-in constraint.
- Subgroup membership is not proved. `enforce_in_group` may be written as the cofactor-doubling equations without claiming that every `groupp` point has a witness or that those equations equal `edwards-bls12-add`.
- A host halt (a string whose length does not fit in `u32`, a constraint or density limit) is not an unsatisfiable R1CS. Record it as a halt. Do not add a constraint snarkVM does not emit in order to flip R1CS-COMPLETE.
