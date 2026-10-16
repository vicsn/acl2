# Charon + Aeneas extraction of two boolean circuits

Boolean AND and XOR, the two smallest snarkVM circuits that emit a constraint
(`circuit/types/boolean/src/and.rs` and `xor.rs` at snarkVM `7dc117d45`).

`src/boolean.rs` is that control flow without the `Environment` trait or the
closure passed to `E::enforce`. Constant operands emit nothing. The
variable/variable arm returns the R1CS triple:

- AND: `(self) * (other) = (output)`
- XOR: `(2*self) * (other) = (self + other - output)`

`src/shape.rs` keeps the trait, the closure, and `expect`. Charon accepts it.
Aeneas does not: it cannot name the closure and then aborts in `add_fuel`.

`boolean.lisp` is the book Aeneas writes for `src/boolean.rs`. It is not part
of the Aleo circuit build. It includes `rust-primitives` from the Aeneas
image, so certify it there.

Regenerate and certify with the pinned image
`ghcr.io/bendyarm/aeneas-acl2-dev:aeneas-23cf8c8_charon-58b7d54_acl2-0612757`
(Aeneas `23cf8c88`, Charon `58b7d543`, ACL2 `0612757b`):

```sh
books/projects/aleo/vm/circuits/aeneas-extraction/extract.sh
```

The script checks that the new book matches `boolean.lisp`, certifies that
book, and checks that `src/shape.rs` still fails to extract. `^` on `bool` is
written as `!=` because the ACL2 backend rejects that lowering as a wrapping
shift. The helper is `mk_term`, not `term`, because the FTY product for
`Term` already defines `boolean-term`.
