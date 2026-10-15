# hash.psd2 and hash.psd4: Axe and PFCS

Both opcodes are Poseidon on the BLS12-377 scalar field, alpha 17, capacity 1,
4 full rounds, 31 partial rounds, 4 full rounds. Partial rounds S-box only the
capacity word. Capacity words come first and the rate index ascends.
`hash.psd2` is rate 2 with domain separator `"Poseidon2"`
(930294893155900944208). `hash.psd4` is rate 4 with `"Poseidon4"`
(967188381303320047440). The preimage is domain, length, then `rate - 2` zeros,
then the inputs, so rate 2 adds no zeros and rate 4 adds two. One output is
squeezed. The specifications are `poseidon::hash2` and `poseidon::hash4`.

snarkVM emits a constraint only for a product. Additions, scalings, and the MDS
matrix stay in linear combinations. An S-box whose input is constant is folded
away. Each remaining S-box is five multiplications (`x^2`, `x^4`, `x^8`,
`x^16`, `x^17`). The first permutation of an all-constant prefix disappears. A
later permutation folds only the still-constant capacity word on its first
round; the MDS then mixes the variable into every word. That gives the sample
counts below. A WEF sample adds one dummy multiplication by a wire fixed to 1
so the output is a single wire. The Axe proofs use the WEF samples.

| Sample | Non-constant S-boxes | Raw constraints | WEF constraints |
| --- | ---: | ---: | ---: |
| rate 2, 0 inputs | 0 | 0 | — |
| rate 2, 1 input | 53 | 265 | 266 |
| rate 2, 3 inputs | 109 | 545 | 546 |
| rate 4, 0 inputs | 0 | 0 | — |
| rate 4, 1 input | 67 | 335 | 336 |
| rate 4, 5 inputs | 141 | 705 | 706 |

## Axe

The scripts live in `circuits/axe/`:

- `poseidon-rate2-1.lisp` lifts the one-input rate-2 WEF sample and proves that
  its constraints imply `(equal out (poseidon::hash2 (list in)))`. It is
  included from `top-keccak-poseidon.lisp`.
- `poseidon-rate2-3.lisp` does the same for three inputs. The proof form is
  live. The file is not in that top.
- `poseidon-rate4-1.lisp` lifts the one-input rate-4 sample. The proof is
  commented out: it needs `pfield::add-commutative-2-axe`, and that run has not
  been seen to finish. There is no rate-4 five-input proof file.

Each proof is soundness for one fixed length. Variable indices are those of
the sample (`w0` input and `w267` output for rate 2 with one input; `w548 = 1`
and `w549` output for three inputs; `w336 = 1` and `w337` output for rate 4).
`lift-r1cs` and `prove-implication-with-r1cs-prover` sit outside the logic.

## PFCS

`circuits/pfcs/poseidon-pow17.lisp` is the five-multiplication S-box.
`pow17-pred-to-spec` proves it equivalent to the successive powers, both ways,
so the intermediates are unique. `circuits/pfcs/hash-psd.lisp` is one generator,
`hash-psd-circuit`, with wrappers `hash-psd2-circuit` and `hash-psd4-circuit`.
It runs the same sponge as `poseidon::absorb` / `squeeze`, constant-folds the
same S-boxes, and calls `pow17` on variables. A linear combination that is about
to be multiplied is bound by `(lc) * (1) == (w)`, which structured R1CS requires
before a relation call. Inlining those binds is the sample shape. The output is
bound the same way.

`assert-event` checks the S-box counts above (0 / 53 / 109 and 0 / 67 / 141)
and the body lengths 107 and 135 for the one-input circuits (one `pow17`, one
bind per S-box, plus the output bind). Those events run at certification time.
This environment has no ACL2, so they have not been run here.

The hash-level statement is: for every length below the prime,
`hash_psd2(in_0, ..., in_{n-1}, out)` holds iff `out` is
`(poseidon::hash2 inputs)`, and likewise `hash_psd4` with `hash4`. That
equivalence is not proved. `pfcs::lift` lifts one definition; it does not lift
this family.

## Comparison

Axe proves the artifact that snarkVM emitted. For `hash.psd2` at one and three
inputs, the WEF constraints imply `poseidon::hash2`. The rewriting absorbs the
flat DAG, including the linear combinations that snarkVM never materialized.
The cost is one script per length, sample-specific wire names, a hand-tuned
rule list, and a rate-4 proof that does not finish. Only soundness is claimed,
only two lengths are proved, and only the one-input rate-2 proof is in the top
bundle. The lifted DAG does not compose with other PFCS or R1CS proofs.

PFCS states the opcode as a family. One generator covers both rates and every
length, including the empty input, and the S-box is a named relation with a
proved equivalence. The same constant-folding produces the sample S-box counts.
Structured R1CS makes the binds explicit, and inlining them is the sample. The
hash equivalence itself is unchecked, the round constants live in the
generator, and the extra binds mean a PFCS definition is a model of the sample
until those binds are removed. That removal is not proved, so a PFCS definition
does not by itself certify a snarkVM sample. Symbolic execution of the
permutation is the certification cost; it is the cost of building the circuit,
which is small next to rewriting the flat Axe DAG.

Use the PFCS for the opcode as a family and for the S-box. Use the Axe proofs
as the machine-checked link from a concrete sample to `poseidon::hash2`, for
the two lengths where that proof exists. They describe the same constraint
system once the PFCS binds are inlined. That last equivalence is open, as is
`hash.psd4` and every length other than the two proved rate-2 samples.
