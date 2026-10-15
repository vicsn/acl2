#!/usr/bin/env python3
"""Sample snarkVM circuits and check them against the formal R1CS specs.

The snarkVM tree must contain the scope sampler (``maybe_write_scope_sample``).
That change lives on ``github.com/vicsn/snarkVM`` and as
``books/projects/aleo/vm/snarkVM-sample.patch`` against commit 7dc117d45.
The Literal::new samples also need
``books/projects/aleo/vm/snarkVM-literal-new-sample.patch`` and
``books/projects/aleo/vm/snarkVM-scalar-new-range-check.patch``.  Without
the range check, Scalar::new and Signature::new fail their checks: the
formal Scalar::new gadget is the patched one, and the unpatched circuit
accepts a wire in [r, p) (scalar-new-unpatched-accepts-non-scalar).

Usage:
  python3 aleovm_sample_circuits.py --snarkvm /path/to/snarkVM
  python3 aleovm_sample_circuits.py --snarkvm /path/to/snarkVM --all

``--all`` runs every non-excluded circuit package's library tests, which is
slow.  The default runs the deterministic ``sample_*`` tests and checks the
JSON they write against the gadgets in
``books/projects/aleo/vm/circuits/fun-circuits``.
"""

import argparse
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))

# scope -> expected check.  Shapes ignore variable names and coefficients of ONE
# versus a public one, and only require these shapes to occur, in order, as a
# subsequence of the dumped constraints (input boolean checks may precede them).
#
# xor: (2*x)*(y) = (x + y - z)     three terms on C, coeff 2 on A
# and: (x)*(y) = (z)               one term each
# or:  (1-x)*(1-y) = (1-z)         two terms on A, B and C
# mul: (x)*(y) = (z)               same shape as and; distinguished by scope
# assert: (b)*(1) = (1)            C is ONE
# assert_eq: (a)*(1) = (b)
# assert_neq / is_zero / is_one: two constraints, second C empty

def terms(side):
    return [(name, coeff) for name, coeff in side]


def shape(constraint):
    a, b, c = terms(constraint["a"]), terms(constraint["b"]), terms(constraint["c"])
    def brief(side):
        return tuple(sorted((("ONE" if name in ("ONE", "p0") else "v"), coeff) for name, coeff in side))
    return (brief(a), brief(b), brief(c), len(a), len(b), len(c))


def is_xor(constraint):
    a, b, c = constraint["a"], constraint["b"], constraint["c"]
    return (len(a) == 1 and a[0][1] == "2"
            and len(b) == 1 and b[0][1] == "1"
            and len(c) == 3)


def is_and(constraint):
    a, b, c = constraint["a"], constraint["b"], constraint["c"]
    return (len(a) == 1 and a[0][1] == "1"
            and len(b) == 1 and b[0][1] == "1"
            and len(c) == 1 and c[0][1] == "1")


def is_or(constraint):
    return len(constraint["a"]) == 2 and len(constraint["b"]) == 2 and len(constraint["c"]) == 2


def is_bool_check(constraint):
    return len(constraint["a"]) == 2 and len(constraint["b"]) == 1 and constraint["c"] == []


def is_mul_by_one_to_var(constraint):
    """(x)*(1) = (y), y a variable."""
    a, b, c = constraint["a"], constraint["b"], constraint["c"]
    return (len(a) == 1 and a[0][1] == "1"
            and len(b) == 1 and b[0][0] in ("ONE", "p0") and b[0][1] == "1"
            and len(c) == 1 and c[0][1] == "1" and c[0][0] not in ("ONE", "p0"))


def is_assert_true(constraint):
    a, b, c = constraint["a"], constraint["b"], constraint["c"]
    return (len(a) == 1 and a[0][1] == "1"
            and len(b) == 1 and b[0][0] in ("ONE", "p0")
            and len(c) == 1 and c[0][0] in ("ONE", "p0") and c[0][1] == "1")


def is_neq_pair(constraints):
    """Two constraints (delta)*(m) = (r) and (delta)*(1-r) = 0."""
    if len(constraints) < 2:
        return False
    first, second = constraints[-2], constraints[-1]
    return (is_and(first) or (len(first["a"]) >= 1 and len(first["b"]) == 1 and len(first["c"]) == 1)
            and second["c"] == []
            and len(second["a"]) >= 1
            and len(second["b"]) == 2)


def count(pred, constraints):
    return sum(1 for c in constraints if pred(c))


def has_coeff(constraint, coeff):
    return any(term[1] == coeff
               for side in (constraint["a"], constraint["b"], constraint["c"])
               for term in side)


def is_group_inject(constraints):
    """enforce_in_group: 13 constraints, curve constant d = 3021 once."""
    return (len(constraints) == 13
            and count(lambda c: has_coeff(c, "3021"), constraints) == 1
            and count(is_bool_check, constraints) == 0)


def is_literal_identifier(constraints):
    """31 bytes: 248 boolean checks, 31 validate_byte bodies, 30 trailing nulls.
    809 = 248 + 21 + 30*17 + 30.  The first byte adds the letter assert."""
    return (len(constraints) == 809
            and count(is_bool_check, constraints) == 248
            and count(lambda c: len(c["a"]) == 5, constraints) == 62
            and count(is_xor, constraints) == 31
            and count(is_or, constraints) == 62
            and count(lambda c: len(c["a"]) == 1 and len(c["b"]) == 2 and c["c"] == [],
                      constraints) == 30
            and count(is_assert_true, constraints) == 1)


SCALAR_MODULUS = 2111115437357092606062206234695386632838870926408408195193685246394721360383


def is_pow2sum(constraint, n):
    """(s)*(1) = (b_0 + 2 b_1 + ... + 2^(n-1) b_(n-1))."""
    a, b, c = constraint["a"], constraint["b"], constraint["c"]
    return (len(a) == 1 and a[0][1] == "1"
            and len(b) == 1 and b[0][0] in ("ONE", "p0")
            and [term[1] for term in c] == [str(2 ** i) for i in range(n)])


def is_assert_zero(constraint):
    """(1 - r)*(1) = (1)."""
    a, b, c = constraint["a"], constraint["b"], constraint["c"]
    return (len(a) == 2 and any(name in ("ONE", "p0") for name, _ in a)
            and len(b) == 1 and b[0][0] in ("ONE", "p0")
            and len(c) == 1 and c[0][0] in ("ONE", "p0"))


def is_literal_scalar(constraints):
    """Scalar::new with snarkVM-scalar-new-range-check.patch: 251 boolean
    checks, the weighted-sum assert_eq, the comparison chain against r - 1
    (AND on a 1 bit, OR on a 0 bit, bit 0 folded), and the final assert.
    503 constraints.  Unpatched snarkVM emits none, which accepts [r, p)."""
    bits = bin(SCALAR_MODULUS - 1)[2:][::-1]
    return (len(constraints) == 503
            and all(is_bool_check(c) for c in constraints[:251])
            and is_pow2sum(constraints[251], 251)
            and count(is_and, constraints[252:502]) == bits[1:].count("1")
            and count(is_or, constraints[252:502]) == bits[1:].count("0")
            and is_assert_zero(constraints[502]))


def is_literal_signature(constraints):
    """Two patched Scalar::new (1006), two Group::new (26), and
    hash_to_scalar_psd4 of the x-coordinates.  The hash is excluded; this
    sample's private-mode count for it is 847, so 1879."""
    return (len(constraints) == 1879
            and count(lambda c: has_coeff(c, "3021"), constraints) == 2
            and count(lambda c: is_pow2sum(c, 251), constraints) == 2)


CHECKS = {
    "sample_enforce": lambda cs: len(cs) == 1 and is_and(cs[0]),
    "sample_assert": lambda cs: len(cs) == 1 and is_assert_true(cs[0]),
    "sample_assert_eq": lambda cs: len(cs) == 1 and is_mul_by_one_to_var(cs[0]),
    "sample_assert_neq": lambda cs: len(cs) == 1 and cs[0]["c"] and cs[0]["c"][0][0] in ("ONE", "p0"),
    "sample_boolean_adder": lambda cs: (
        sum(is_xor(c) for c in cs) == 2
        and sum(is_and(c) for c in cs) >= 2
        and sum(is_or(c) for c in cs) == 1
        and sum(is_bool_check(c) for c in cs) == 3
    ),
    "sample_boolean_subtractor": lambda cs: (
        sum(is_xor(c) for c in cs) == 2
        and sum(is_or(c) for c in cs) == 1
        and sum(is_bool_check(c) for c in cs) == 3
        and len(cs) == 8  # 3 boolean checks + 2 xor + 2 and-not + 1 or
    ),
    "sample_field_is_zero": is_neq_pair,
    "sample_field_is_one": is_neq_pair,
    "sample_field_is_equal": is_neq_pair,
    "sample_field_is_not_equal": is_neq_pair,
    "sample_literal_boolean": lambda cs: len(cs) == 1 and is_bool_check(cs[0]),
    "sample_literal_field": lambda cs: cs == [],
    "sample_literal_scalar": is_literal_scalar,
    "sample_literal_u8": lambda cs: len(cs) == 8 and all(is_bool_check(c) for c in cs),
    "sample_literal_string": lambda cs: (
        len(cs) == 17
        and cs[0]["a"] == [["ONE", "2"]]
        and cs[0]["b"] == [["ONE", "1"]]
        and len(cs[0]["c"]) == 1
        and all(is_bool_check(c) for c in cs[1:])
    ),
    "sample_literal_group": is_group_inject,
    "sample_literal_address": is_group_inject,
    "sample_literal_identifier": is_literal_identifier,
    "sample_literal_signature": is_literal_signature,
}


def run(cmd, env, cwd):
    print("+", " ".join(cmd), flush=True)
    proc = subprocess.run(cmd, cwd=cwd, env=env)
    if proc.returncode != 0:
        sys.exit(proc.returncode)


def sample_packages(snarkvm, outdir, packages):
    env = os.environ.copy()
    env["ALEOVM_SAMPLE_DIR"] = outdir
    os.makedirs(outdir, exist_ok=True)
    for package, test_filter in packages:
        cmd = ["cargo", "test", "-p", package, "--lib", test_filter, "--", "--test-threads=8"]
        run(cmd, env, snarkvm)


def load_samples(outdir):
    samples = []
    for name in sorted(os.listdir(outdir)):
        if not name.endswith(".json"):
            continue
        with open(os.path.join(outdir, name)) as f:
            try:
                samples.append(json.load(f))
            except json.JSONDecodeError as exc:
                print(f"invalid JSON {name}: {exc}")
    return samples


def check(samples):
    by_scope = {}
    for sample in samples:
        by_scope.setdefault(sample.get("scope", ""), []).append(sample)
    failed = False
    for scope, pred in CHECKS.items():
        found = by_scope.get(scope, [])
        if not found:
            print(f"MISSING sample for {scope}")
            failed = True
            continue
        sample = found[0]
        cs = sample["constraints"]
        if not sample.get("is_satisfied", False):
            print(f"UNSATISFIED {scope}")
            failed = True
            continue
        if not pred(cs):
            print(f"SHAPE MISMATCH {scope}: {len(cs)} constraints")
            print(json.dumps(cs, indent=2)[:2000])
            failed = True
            continue
        print(f"ok {scope}: {len(cs)} constraints")
    return not failed


DEFAULT_PACKAGES = [
    ("snarkvm-circuit-environment", "sample_"),
    ("snarkvm-circuit-types-boolean", "sample_"),
    ("snarkvm-circuit-types-field", "sample_"),
    ("snarkvm-circuit-program", "sample_literal"),
]


def all_circuit_packages(snarkvm):
    packages = []
    circuit = os.path.join(snarkvm, "circuit")
    for dirpath, dirnames, filenames in os.walk(circuit):
        if "Cargo.toml" in filenames and "target" not in dirpath.split(os.sep):
            text = open(os.path.join(dirpath, "Cargo.toml")).read()
            for line in text.splitlines():
                if line.startswith("name = "):
                    name = line.split("=", 1)[1].strip().strip('"')
                    if name.startswith("snarkvm-circuit"):
                        packages.append((name, ""))
                    break
        dirnames[:] = [d for d in dirnames if d != "target"]
    return packages


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snarkvm", required=True, help="path to a snarkVM checkout at 7dc117d45 or later, with the sampler")
    parser.add_argument("--out", default=os.path.join(ROOT, "books/projects/aleo/vm/circuits/fun-circuits/samples"))
    parser.add_argument("--all", action="store_true", help="sample every circuit package's library tests")
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    if not args.check_only:
        packages = all_circuit_packages(args.snarkvm) if args.all else DEFAULT_PACKAGES
        if args.all:
            # Drop the hash crates: they are excluded from formalisation and dominate runtime.
            packages = [p for p in packages if "algorithm" not in p[0]]
        sample_packages(args.snarkvm, args.out, packages)
    samples = load_samples(args.out)
    print(f"{len(samples)} sample files")
    if not check(samples):
        sys.exit(1)


if __name__ == "__main__":
    main()
