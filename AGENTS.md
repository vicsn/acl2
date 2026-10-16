# AleoVM circuit formalisation

Circuit work is recorded in two places that must move together:

- `aleovm_circuit_function_formalisation_status.csv` at the repository root
- `books/projects/aleo/vm/circuits/fun-specs/README.md`

## Status table

Do not hand-edit flag columns in the CSV. `aleovm_circuit_functions_scan.py` regenerates the file from the snarkVM `circuit/` tree, from `ACL2_MODELS`, from `aleovm_circuit_function_funspec_map.tsv` (FUN-SPEC only), and from `aleovm_circuit_function_circspec_map.tsv` (the five circuit flags, `R1CS-SOUND-IF`, and `R1CS-COMPLETE-IF`). `STATUS` is derived.

```
python3 aleovm_circuit_functions_scan.py <snarkVM>/circuit aleovm_circuit_function_formalisation_status.csv
```

The root argument must be the `circuit/` directory so paths look like `circuit/...`. The tree is snarkVM commit `7dc117d45` (2026-10-14), not the 2023 submodule under `books/projects/aleo/vm/snarkVM`.

When a circuit task is finished:

- Add a row to `aleovm_circuit_function_circspec_map.tsv`. A column value `1` sets that flag. A `0` does not clear a `1` already recorded from `ACL2_MODELS` or from an earlier map row.
- Do not clear an existing `1`, unless a finding shows the proof did not establish it (for example a soundness theorem that assumed its conclusion). Then set it to `0` and record the finding under **Open TODOs** in the same change.
- Leave rows whose FUN-SPEC is `excluded` (the hash and algorithm internals) unchanged.
- Set a flag to `1` only after `books/build/cert.pl` has accepted the book named in the `acl2` column.
- Regenerate the CSV in the same change as the book.

The columns mean:

- **R1CS-SPEC / PFCS-SPEC.** The formal constraints are the ones snarkVM emits. A fully constant triple is checked by the host and is not a constraint. Boolean NOT and field addition are linear combinations; do not add a constraint for them. A PFCS definition that lowers to that R1CS discharges both columns.
- **R1CS-SAMPLES.** `python3 aleovm_sample_circuits.py --snarkvm <snarkVM>` rebuilds the scope dumps and checks their shapes. The sampler lives on `github.com/vicsn/snarkVM` branch `aleovm-scope-samples` and in `books/projects/aleo/vm/snarkVM-sample.patch` (plus `snarkVM-literal-new-sample.patch`). Where the formal circuit is a fix of snarkVM, the fix is a patch next to them (`snarkVM-scalar-new-range-check.patch`) and the checks only pass on the patched tree.
- **R1CS-SOUND.** Every satisfying assignment of the formal circuit has I/O that matches the funspec. State it over the wires: build the output from the values in the assignment, prove the type predicate of those values (a constructor that fixes its argument hides an out-of-range wire), and prove the funspec returns that output. A theorem that takes a well-typed literal as a hypothesis is not unconditional R1CS-SOUND. To show a gap in snarkVM, prove a satisfying assignment of the unpatched gadget whose output fails the type predicate.
- **R1CS-SOUND-IF.** Copied from the circspec map. It is not a 0/1 flag. Empty, with R1CS-SOUND 1, means the theorem is unconditional. A non-empty cell names the prior circuit that already constrained the same value, and R1CS-SOUND is then 1 only together with that circuit. The cell stays empty, and R1CS-SOUND stays 0, when no such circuit discharges the hypothesis. A mathematical hypothesis such as `edwards-bls12-cofactor-clears` is not a circuit conjunction. An incomplete proof (multiplication, exponentiation, shifts, signed or 128-bit division) stays 0 even if `Integer::new` would type the inputs.
- **R1CS-COMPLETE.** Every funspec input that returns a value has a satisfying assignment, and an input on which the funspec returns `(spec-error)` has none.
- **R1CS-COMPLETE-IF.** Copied from the circspec map, like `R1CS-SOUND-IF`. A non-empty cell names the prior circuit whose satisfying assignment supplies the witness the completeness theorem assumes. A witness that is assumed but that no circuit produces (for example a cofactor witness for every `groupp` point) is not a circuit conjunction; leave the cell empty.
- **STATUS.** Derived by the scan, not set in any map: `verified` when R1CS-SOUND is 1 or `R1CS-SOUND-IF` is non-empty, and R1CS-COMPLETE is 1 or `R1CS-COMPLETE-IF` is non-empty. Otherwise empty.

Higher-level gadgets call the lower-level ones (`boolean-check-gadget`, `boolean-check-gadget-list`, `enforce-gadget`, `assert-eq-gadget`, `assert-gadget`, and the gadgets under `fun-circuits/`) instead of restating them.

## Call graph

`aleovm_circuit_call_graph.canvas.tsx` draws every row of the status CSV as a node, coloured by its flags, with an edge from each function to the circuit functions it calls. Its data block, between `BEGIN GENERATED DATA` and `END GENERATED DATA`, comes from the same snarkVM tree and the CSV:

```
python3 aleovm_circuit_call_graph.py <snarkVM>/circuit
```

The graph must stay up to date. Rerun the script whenever the CSV is regenerated or `aleovm_circuit_functions_scan.py` changes, and commit the canvas in the same change. Do not hand-edit the data block. The script exits with status 1 and prints the cycle when the resolved calls are not acyclic; fix the resolution rule rather than the data. A call the parser can only match by name goes to a dispatch node, not an edge; the script docstring lists which calls count as resolved. To open the canvas in Cursor, copy it into the workspace's `canvases/` directory.

## Fun-spec README

`books/projects/aleo/vm/circuits/fun-specs/README.md` is the list of open limitations. When a proof stops short of a flag, add the gap there in the same change, under **Open TODOs**. In particular:

- Poseidon, BHP, Pedersen, Keccak, and Elligator2 stay abstract. A caller that emits one of those circuits (for example `Signature::new` via `hash_to_scalar_psd4`) uses the abstract funspec equality for that call. Say so in the README; do not invent a stand-in constraint.
- Subgroup membership is not proved. `group-enforce-in-group-sound` proves the `enforce_in_group` output is 4Q under `edwards-bls12-add`; that 4Q is a `groupp` point is the hypothesis `edwards-bls12-cofactor-clears`. A soundness theorem that takes it is conditional, so its flag stays `0`. No book claims that every `groupp` point has a cofactor witness.
- A host halt (a string whose length does not fit in `u32`, a constraint or density limit) is not an unsatisfiable R1CS. Record it as a halt. Do not add a constraint snarkVM does not emit in order to flip R1CS-COMPLETE.
