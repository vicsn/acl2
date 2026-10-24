//! Constraint emission of the snarkVM circuit functions whose rows are
//! `verified` in `aleovm_circuit_function_formalisation_status.csv`.
//!
//! Each function follows the control flow of its snarkVM source at commit
//! `7dc117d45` (the file is named in the doc comment) and records the R1CS
//! triples that source passes to `E::enforce`, in emission order. Only the
//! constraint system is modelled: witness values are not computed, so a
//! `witness!` or `E::new_variable` is a fresh wire.
//!
//! The ACL2 backend has no traits, closures, slices, or `clone`, so the
//! `Environment` is the explicit `Cs` threaded through `&mut`, operator
//! traits are plain functions, and vectors are copied term by term.
//!
//! A linear combination is a list of terms `c * 2^sh * k * v`. Wire `0` is
//! the constant one. `k` indexes `Cs::ks` (in chunks of 256, as a
//! push is linear in the length of the list in ACL2), field constants too large for `c`
//! (named constants and their products, sums and inverses; `0` is the factor
//! one). The checks evaluate them mod p, so the model never folds them. As in snarkVM, a linear combination is constant when it has
//! no variable term left after cancellation, and a triple of constants is
//! checked on the host instead of being emitted.
//!
//! The `h_*` functions at the end are the harnesses: they allocate the input
//! wires without constraints (the input circuits named in `R1CS-SOUND-IF` are
//! separate rows) and run one function in variable mode.

#[derive(Clone, Copy)]
pub struct Term {
    pub c: i128,
    pub sh: u32,
    pub v: u32,
    pub k: u32,
}

/// A field constant: `op` 0 is the named constant `a`, 1 the product of
/// constants `a` and `b`, 2 their sum, 3 the inverse of `a`, 4 `c * 2^sh`.
#[derive(Clone, Copy)]
pub struct Konst {
    pub op: u32,
    pub a: u32,
    pub b: u32,
    pub c: i128,
    pub sh: u32,
}

pub struct Constraint {
    pub a: Vec<Term>,
    pub b: Vec<Term>,
    pub c: Vec<Term>,
}

pub struct Cs {
    pub next: u32,
    pub cs: Vec<Constraint>,
    pub ks: Vec<Vec<Konst>>,
    pub nk: u32,
}

/// BLS12-377 scalar field: `p - 1` and `(p - 1) / 2`, little-endian limbs.
const P_MINUS_ONE: [u64; 4] = [0x0a11800000000000, 0x59aa76fed0000001, 0x60b44d1e5c37b001, 0x12ab655e9a2ca556];
const P_HALF: [u64; 4] = [0x8508c00000000000, 0xacd53b7f68000000, 0x305a268f2e1bd800, 0x0955b2af4d1652ab];
/// The Edwards BLS12 scalar field modulus r, and r - 1.
const R: [u64; 4] = [0xb95aee9ac33fd9ff, 0x5293a3afc43c8afe, 0x982d1347970dec00, 0x04aad957a68b2955];
const R_MINUS_ONE: [u64; 4] = [0xb95aee9ac33fd9fe, 0x5293a3afc43c8afe, 0x982d1347970dec00, 0x04aad957a68b2955];
/// `E::ScalarField::size_in_bits()` and `size_in_data_bits()`.
const SCALAR_BITS: usize = 251;
const SCALAR_DATA_BITS: usize = 250;
/// `E::BaseField::size_in_bits()` and `size_in_data_bits()`.
const FIELD_BITS: usize = 253;
const FIELD_DATA_BITS: usize = 252;

// ---------------------------------------------------------------------------
// Linear combinations

fn tm(c: i128, sh: u32, v: u32) -> Term {
    Term { c, sh, v, k: 0 }
}

fn tm_k(t: Term, c: i128, sh: u32) -> Term {
    Term { c, sh, v: t.v, k: t.k }
}

fn same_k(x: Term, y: Term) -> bool {
    x.k == y.k
}

fn k_push(cs: &mut Cs, op: u32, a: u32, b: u32, c: i128, sh: u32) -> u32 {
    if cs.nk % 256 == 0 {
        cs.ks.push(Vec::new());
    }
    let last = cs.ks.len() - 1;
    cs.ks[last].push(Konst { op, a, b, c, sh });
    cs.nk = cs.nk + 1;
    cs.nk
}

fn k_mul(cs: &mut Cs, a: u32, b: u32) -> u32 {
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else {
        k_push(cs, 1, a, b, 0, 0)
    }
}

/// The product of term `t` and the constant term `k`.
fn term_mul(cs: &mut Cs, t: Term, k: Term) -> Term {
    let kk = k_mul(cs, t.k, k.k);
    Term { c: t.c * k.c, sh: t.sh + k.sh, v: t.v, k: kk }
}

/// A constant linear combination as one constant.
fn lc_to_k(cs: &mut Cs, x: &Vec<Term>) -> u32 {
    let mut acc = k_push(cs, 4, 0, 0, 0, 0);
    let mut i = 0;
    while i < x.len() {
        let n = k_push(cs, 4, 0, 0, x[i].c, x[i].sh);
        let t = k_mul(cs, n, x[i].k);
        acc = k_push(cs, 2, acc, t, 0, 0);
        i += 1;
    }
    acc
}

/// The named constant `name` (an index into the checks' table).
pub fn f_named(cs: &mut Cs, name: u32) -> Field {
    let k = k_push(cs, 0, name, 0, 0, 0);
    let mut lc = Vec::new();
    lc.push(Term { c: 1, sh: 0, v: 0, k });
    f_of(lc)
}

pub fn cs_new() -> Cs {
    Cs { next: 0, cs: Vec::new(), ks: Vec::new(), nk: 0 }
}

pub fn new_var(cs: &mut Cs) -> u32 {
    cs.next += 1;
    cs.next
}

fn lc_zero() -> Vec<Term> {
    Vec::new()
}

fn lc_one() -> Vec<Term> {
    let mut out = Vec::new();
    out.push(tm(1, 0, 0));
    out
}

fn lc_var(v: u32) -> Vec<Term> {
    let mut out = Vec::new();
    out.push(tm(1, 0, v));
    out
}

fn lc_const(c: i128, sh: u32) -> Vec<Term> {
    let mut out = Vec::new();
    if c != 0 {
        out.push(tm(c, sh, 0));
    }
    out
}

fn lc_copy(x: &Vec<Term>) -> Vec<Term> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < x.len() {
        out.push(x[i]);
        i += 1;
    }
    out
}

/// Normalises `c * 2^sh` so that `c` is odd (or the term is zero).
fn term_norm(t: Term) -> Term {
    let mut c = t.c;
    let mut sh = t.sh;
    let mut fuel = 0;
    while c != 0 && c % 2 == 0 && fuel < 128 {
        c = c / 2;
        sh += 1;
        fuel += 1;
    }
    tm_k(t, c, sh)
}

/// The sum of two terms on the same wire, when it fits in one term.
fn term_merge(x: Term, y: Term) -> (bool, Term) {
    if x.c == 0 {
        (true, y)
    } else if y.c == 0 {
        (true, x)
    } else if x.sh == y.sh {
        (true, term_norm(tm_k(x, x.c + y.c, x.sh)))
    } else if small(x.c) && small(y.c) && x.sh < y.sh && y.sh - x.sh < 56 {
        (true, term_norm(tm_k(x, x.c + y.c * pow2(y.sh - x.sh), x.sh)))
    } else if small(x.c) && small(y.c) && y.sh < x.sh && x.sh - y.sh < 56 {
        (true, term_norm(tm_k(x, y.c + x.c * pow2(x.sh - y.sh), y.sh)))
    } else {
        (false, x)
    }
}

fn small(c: i128) -> bool {
    c < 1152921504606846976 && c > 0 - 1152921504606846976
}

fn pow2(k: u32) -> i128 {
    let mut out: i128 = 1;
    let mut i = 0;
    while i < k {
        out = out * 2;
        i += 1;
    }
    out
}

/// Adds one term into a linear combination, merging it with a term on the
/// same wire and dropping a zero coefficient, as `LinearCombination` does.
fn lc_push(x: Vec<Term>, t: Term) -> Vec<Term> {
    if t.c == 0 {
        return x;
    }
    let mut out = Vec::new();
    let mut merged = false;
    let mut i = 0;
    while i < x.len() {
        let u = x[i];
        if !merged && u.v == t.v && same_k(u, t) {
            let (ok, m) = term_merge(u, t);
            if ok {
                merged = true;
                if m.c != 0 {
                    out.push(m);
                }
            } else {
                out.push(u);
            }
        } else {
            out.push(u);
        }
        i += 1;
    }
    if !merged {
        out.push(term_norm(t));
    }
    out
}

/// The constant `c * 2^sh * k` of term `t` as one arena entry.
fn term_k(cs: &mut Cs, t: Term) -> u32 {
    let n = k_push(cs, 4, 0, 0, t.c, t.sh);
    k_mul(cs, n, t.k)
}

fn lc_find_var(x: &Vec<Term>, v: u32) -> usize {
    let mut out = x.len();
    let mut i = 0;
    while i < x.len() {
        if out == x.len() && x[i].v == v {
            out = i;
        }
        i += 1;
    }
    out
}

fn lc_replace(x: &Vec<Term>, j: usize, t: Term) -> Vec<Term> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < x.len() {
        if i == j {
            out.push(t);
        } else {
            out.push(x[i]);
        }
        i += 1;
    }
    out
}

fn lc_compact_push(cs: &mut Cs, x: Vec<Term>, t: Term) -> Vec<Term> {
    let tk = term_k(cs, t);
    let j = lc_find_var(&x, t.v);
    if j < x.len() {
        let k = k_push(cs, 2, x[j].k, tk, 0, 0);
        lc_replace(&x, j, Term { c: 1, sh: 0, v: t.v, k })
    } else {
        let mut out = lc_copy(&x);
        out.push(Term { c: 1, sh: 0, v: t.v, k: tk });
        out
    }
}

/// One term per wire, its coefficient folded into the arena. Without it,
/// terms with different constants never merge and the partial rounds of
/// Poseidon multiply the length of each state element by the width.
fn lc_compact(cs: &mut Cs, x: &Vec<Term>) -> Vec<Term> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < x.len() {
        out = lc_compact_push(cs, out, x[i]);
        i += 1;
    }
    out
}

fn lc_add(x: &Vec<Term>, y: &Vec<Term>) -> Vec<Term> {
    let mut out = lc_copy(x);
    let mut i = 0;
    while i < y.len() {
        out = lc_push(out, y[i]);
        i += 1;
    }
    out
}

fn lc_scale(x: &Vec<Term>, c: i128, sh: u32) -> Vec<Term> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < x.len() {
        let t = x[i];
        out = lc_push(out, tm_k(t, t.c * c, t.sh + sh));
        i += 1;
    }
    out
}

fn lc_neg(x: &Vec<Term>) -> Vec<Term> {
    lc_scale(x, 0 - 1, 0)
}

fn lc_sub(x: &Vec<Term>, y: &Vec<Term>) -> Vec<Term> {
    lc_add(x, &lc_neg(y))
}

/// `LinearCombination::is_constant`: no variable term.
fn lc_is_const(x: &Vec<Term>) -> bool {
    let mut i = 0;
    let mut out = true;
    while i < x.len() {
        if x[i].v != 0 {
            out = false;
        }
        i += 1;
    }
    out
}

/// The product of a linear combination and a constant one.
fn lc_mul_const(cs: &mut Cs, x: &Vec<Term>, k: &Vec<Term>) -> Vec<Term> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < k.len() {
        let mut j = 0;
        while j < x.len() {
            let t = term_mul(cs, x[j], k[i]);
            out = lc_push(out, t);
            j += 1;
        }
        i += 1;
    }
    out
}

/// `E::enforce(|| (a, b, c))`. A constant triple is checked on the host.
pub fn enforce(cs: &mut Cs, a: Vec<Term>, b: Vec<Term>, c: Vec<Term>) {
    if !(lc_is_const(&a) && lc_is_const(&b) && lc_is_const(&c)) {
        cs.cs.push(Constraint { a, b, c });
    }
}

// ---------------------------------------------------------------------------
// circuit/environment/src/environment.rs

/// `E::assert(b)`: `(b) * (1) = (1)`.
pub fn env_assert(cs: &mut Cs, b: &Vec<Term>) {
    enforce(cs, lc_copy(b), lc_one(), lc_one());
}

/// `E::assert_eq(a, b)`: `(a) * (1) = (b)`.
pub fn env_assert_eq(cs: &mut Cs, a: &Vec<Term>, b: &Vec<Term>) {
    enforce(cs, lc_copy(a), lc_one(), lc_copy(b));
}

/// `E::assert_neq(a, b)`: a witnessed multiplier `m` with `(a - b) * (m) = (1)`.
pub fn env_assert_neq(cs: &mut Cs, a: &Vec<Term>, b: &Vec<Term>) {
    let a_minus_b = lc_sub(a, b);
    let m = if lc_is_const(&a_minus_b) { lc_zero() } else { lc_var(new_var(cs)) };
    enforce(cs, a_minus_b, m, lc_one());
}

// ---------------------------------------------------------------------------
// circuit/types/boolean

/// A boolean is a linear combination; `k` is its value when it is constant.
pub struct Boolean {
    pub lc: Vec<Term>,
    pub k: bool,
}

pub fn b_const(k: bool) -> Boolean {
    Boolean { lc: if k { lc_one() } else { lc_zero() }, k }
}

fn b_var(v: u32) -> Boolean {
    Boolean { lc: lc_var(v), k: false }
}

fn b_copy(x: &Boolean) -> Boolean {
    Boolean { lc: lc_copy(&x.lc), k: x.k }
}

fn b_is_const(x: &Boolean) -> bool {
    lc_is_const(&x.lc)
}

/// `Boolean::new(Mode::Private, _)` (lib.rs): `(1 - b) * (b) = (0)`.
pub fn b_new(cs: &mut Cs) -> Boolean {
    let v = new_var(cs);
    enforce(cs, lc_sub(&lc_one(), &lc_var(v)), lc_var(v), lc_zero());
    b_var(v)
}

/// not.rs: a constant is flipped; a variable is the linear form `1 - b`.
pub fn b_not(x: &Boolean) -> Boolean {
    if b_is_const(x) {
        b_const(!x.k)
    } else {
        Boolean { lc: lc_sub(&lc_one(), &x.lc), k: false }
    }
}

/// and.rs `bitand_assign`: `(self) * (other) = (output)`.
pub fn b_and(cs: &mut Cs, x: &Boolean, y: &Boolean) -> Boolean {
    if b_is_const(x) {
        if x.k { b_copy(y) } else { b_copy(x) }
    } else if b_is_const(y) {
        if y.k { b_copy(x) } else { b_copy(y) }
    } else {
        let out = b_var(new_var(cs));
        enforce(cs, lc_copy(&x.lc), lc_copy(&y.lc), lc_copy(&out.lc));
        out
    }
}

/// or.rs `bitor_assign`: `(1 - self) * (1 - other) = (1 - output)`.
pub fn b_or(cs: &mut Cs, x: &Boolean, y: &Boolean) -> Boolean {
    if b_is_const(x) {
        if x.k { b_copy(x) } else { b_copy(y) }
    } else if b_is_const(y) {
        if y.k { b_copy(y) } else { b_copy(x) }
    } else {
        let out = b_var(new_var(cs));
        enforce(
            cs,
            lc_sub(&lc_one(), &x.lc),
            lc_sub(&lc_one(), &y.lc),
            lc_sub(&lc_one(), &out.lc),
        );
        out
    }
}

/// xor.rs `bitxor_assign`: `(self + self) * (other) = (self + other - output)`.
pub fn b_xor(cs: &mut Cs, x: &Boolean, y: &Boolean) -> Boolean {
    if b_is_const(x) {
        if x.k { b_not(y) } else { b_copy(y) }
    } else if b_is_const(y) {
        if y.k { b_not(x) } else { b_copy(x) }
    } else {
        let out = b_var(new_var(cs));
        enforce(cs, lc_add(&x.lc, &x.lc), lc_copy(&y.lc), lc_sub(&lc_add(&x.lc, &y.lc), &out.lc));
        out
    }
}

/// nand.rs: `(self) * (other) = (1 - output)`.
pub fn b_nand(cs: &mut Cs, x: &Boolean, y: &Boolean) -> Boolean {
    if b_is_const(x) {
        if x.k { b_not(y) } else { b_not(x) }
    } else if b_is_const(y) {
        if y.k { b_not(x) } else { b_not(y) }
    } else {
        let out = b_var(new_var(cs));
        enforce(cs, lc_copy(&x.lc), lc_copy(&y.lc), lc_sub(&lc_one(), &out.lc));
        out
    }
}

/// nor.rs: `(1 - self) * (1 - other) = (output)`.
pub fn b_nor(cs: &mut Cs, x: &Boolean, y: &Boolean) -> Boolean {
    if b_is_const(x) {
        if x.k { b_not(x) } else { b_not(y) }
    } else if b_is_const(y) {
        if y.k { b_not(y) } else { b_not(x) }
    } else {
        let out = b_var(new_var(cs));
        enforce(cs, lc_sub(&lc_one(), &x.lc), lc_sub(&lc_one(), &y.lc), lc_copy(&out.lc));
        out
    }
}

/// equal.rs: `is_not_equal` is XOR and `is_equal` its negation.
pub fn b_is_not_equal(cs: &mut Cs, x: &Boolean, y: &Boolean) -> Boolean {
    b_xor(cs, x, y)
}

pub fn b_is_equal(cs: &mut Cs, x: &Boolean, y: &Boolean) -> Boolean {
    let r = b_is_not_equal(cs, x, y);
    b_not(&r)
}

/// ternary.rs: `(condition) * (first - second) = (output - second)`.
pub fn b_ternary(cs: &mut Cs, cond: &Boolean, first: &Boolean, second: &Boolean) -> Boolean {
    if b_is_const(cond) {
        if cond.k { b_copy(first) } else { b_copy(second) }
    } else if b_is_const(first) {
        if first.k {
            b_or(cs, cond, second)
        } else {
            let nc = b_not(cond);
            b_and(cs, &nc, second)
        }
    } else if b_is_const(second) {
        if second.k {
            let nc = b_not(cond);
            b_or(cs, &nc, first)
        } else {
            b_and(cs, cond, first)
        }
    } else {
        let out = b_var(new_var(cs));
        enforce(cs, lc_copy(&cond.lc), lc_sub(&first.lc, &second.lc), lc_sub(&out.lc, &second.lc));
        out
    }
}

pub struct SumCarry {
    pub sum: Boolean,
    pub carry: Boolean,
}

/// helpers/adder.rs.
pub fn b_adder(cs: &mut Cs, x: &Boolean, y: &Boolean, carry: &Boolean) -> SumCarry {
    let c0 = b_xor(cs, x, y);
    let sum = b_xor(cs, &c0, carry);
    let c1 = b_and(cs, x, y);
    let c2 = b_and(cs, carry, &c0);
    let carry = b_or(cs, &c1, &c2);
    SumCarry { sum, carry }
}

/// helpers/subtractor.rs.
pub fn b_subtractor(cs: &mut Cs, x: &Boolean, y: &Boolean, borrow: &Boolean) -> SumCarry {
    let c0 = b_xor(cs, x, y);
    let difference = b_xor(cs, &c0, borrow);
    let nx = b_not(x);
    let c1 = b_and(cs, &nx, y);
    let nc0 = b_not(&c0);
    let c2 = b_and(cs, borrow, &nc0);
    let borrow = b_or(cs, &c1, &c2);
    SumCarry { sum: difference, carry: borrow }
}

fn bits_copy(x: &Vec<Boolean>) -> Vec<Boolean> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < x.len() {
        out.push(b_copy(&x[i]));
        i += 1;
    }
    out
}

fn bits_range(x: &Vec<Boolean>, lo: usize, hi: usize) -> Vec<Boolean> {
    let mut out = Vec::new();
    let mut i = lo;
    while i < hi && i < x.len() {
        out.push(b_copy(&x[i]));
        i += 1;
    }
    out
}

fn bits_rev(x: &Vec<Boolean>) -> Vec<Boolean> {
    let mut out = Vec::new();
    let mut i = x.len();
    while i > 0 {
        i -= 1;
        out.push(b_copy(&x[i]));
    }
    out
}

fn bits_append(x: &Vec<Boolean>, y: &Vec<Boolean>) -> Vec<Boolean> {
    let mut out = bits_copy(x);
    let mut i = 0;
    while i < y.len() {
        out.push(b_copy(&y[i]));
        i += 1;
    }
    out
}

/// helpers/bits_are_zero.rs: `assert_eq(sum of bits, 0)`.
pub fn b_assert_bits_are_zero(cs: &mut Cs, bits: &Vec<Boolean>) {
    let mut sum = lc_zero();
    let mut i = 0;
    while i < bits.len() {
        sum = lc_add(&sum, &bits[i].lc);
        i += 1;
    }
    env_assert_eq(cs, &sum, &lc_zero());
}

/// helpers/comparator.rs: fold from the constant `false`, LSB first.
pub fn b_is_less_than_or_equal_constant(cs: &mut Cs, bits: &Vec<Boolean>, consts: &Vec<bool>) -> Boolean {
    let mut rest = b_const(false);
    let mut i = 0;
    while i < consts.len() && i < bits.len() {
        rest = if consts[i] { b_and(cs, &bits[i], &rest) } else { b_or(cs, &bits[i], &rest) };
        i += 1;
    }
    b_not(&rest)
}

pub fn b_assert_less_than_or_equal_constant(cs: &mut Cs, bits: &Vec<Boolean>, consts: &Vec<bool>) {
    let r = b_is_less_than_or_equal_constant(cs, bits, consts);
    env_assert(cs, &r.lc);
}

fn limbs_bits(l: &[u64; 4], n: usize) -> Vec<bool> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < n {
        let limb = l[i / 64];
        out.push((limb >> ((i % 64) as u32)) & 1 == 1);
        i += 1;
    }
    out
}

/// The little-endian bits of `p - 1` and `(p - 1) / 2`.
pub fn p_minus_one_bits() -> Vec<bool> {
    limbs_bits(&P_MINUS_ONE, FIELD_BITS)
}

pub fn p_half_bits() -> Vec<bool> {
    limbs_bits(&P_HALF, FIELD_BITS)
}

// ---------------------------------------------------------------------------
// circuit/types/field

pub enum Bits {
    None,
    Some(Vec<Boolean>),
}

/// A field element and its cached little-endian bits (`bits_le: OnceCell`).
pub struct Field {
    pub lc: Vec<Term>,
    pub bits: Bits,
}

fn f_of(lc: Vec<Term>) -> Field {
    Field { lc, bits: Bits::None }
}

fn f_var(v: u32) -> Field {
    f_of(lc_var(v))
}

fn f_copy(x: &Field) -> Field {
    let bits = match &x.bits {
        Bits::None => Bits::None,
        Bits::Some(b) => Bits::Some(bits_copy(b)),
    };
    Field { lc: lc_copy(&x.lc), bits }
}

fn f_is_const(x: &Field) -> bool {
    lc_is_const(&x.lc)
}

/// `Field::new(Mode::Private, _)`: a fresh wire, no constraint.
pub fn f_new(cs: &mut Cs) -> Field {
    f_var(new_var(cs))
}

/// helpers/from_boolean.rs and `From<Boolean>`: the same linear combination.
pub fn f_from_boolean(b: &Boolean) -> Field {
    f_of(lc_copy(&b.lc))
}

pub fn f_add(x: &Field, y: &Field) -> Field {
    f_of(lc_add(&x.lc, &y.lc))
}

pub fn f_sub(x: &Field, y: &Field) -> Field {
    f_of(lc_sub(&x.lc, &y.lc))
}

/// mul.rs `mul_assign`.
pub fn f_mul(cs: &mut Cs, x: &Field, y: &Field) -> Field {
    if f_is_const(y) {
        f_of(lc_mul_const(cs, &x.lc, &y.lc))
    } else if f_is_const(x) {
        f_of(lc_mul_const(cs, &y.lc, &x.lc))
    } else {
        let out = f_new(cs);
        enforce(cs, lc_copy(&x.lc), lc_copy(&y.lc), lc_copy(&out.lc));
        out
    }
}

/// square.rs: `self * self`.
pub fn f_square(cs: &mut Cs, x: &Field) -> Field {
    f_mul(cs, x, x)
}

/// inverse.rs: `(self) * (inverse) = (1)`.
pub fn f_inverse(cs: &mut Cs, x: &Field) -> Field {
    if f_is_const(x) {
        let kx = lc_to_k(cs, &x.lc);
        let k = k_push(cs, 3, kx, 0, 0, 0);
        let mut lc = Vec::new();
        lc.push(Term { c: 1, sh: 0, v: 0, k });
        f_of(lc)
    } else {
        let inv = f_new(cs);
        enforce(cs, lc_copy(&x.lc), lc_copy(&inv.lc), lc_one());
        inv
    }
}

/// div.rs `div_assign`: `self * other.inverse()`.
pub fn f_div(cs: &mut Cs, x: &Field, y: &Field) -> Field {
    let inv = f_inverse(cs, y);
    f_mul(cs, x, &inv)
}

/// equal.rs `is_not_equal`: `(delta) * (m) = (is_neq)` and `(delta) * (1 - is_neq) = (0)`.
pub fn f_is_not_equal(cs: &mut Cs, x: &Field, y: &Field) -> Boolean {
    if f_is_const(x) && f_is_const(y) {
        b_const(false)
    } else {
        let is_neq = b_var(new_var(cs));
        let delta = lc_sub(&x.lc, &y.lc);
        let m = if lc_is_const(&delta) { lc_zero() } else { lc_var(new_var(cs)) };
        let is_eq = b_not(&is_neq);
        enforce(cs, lc_copy(&delta), m, lc_copy(&is_neq.lc));
        enforce(cs, delta, is_eq.lc, lc_zero());
        is_neq
    }
}

pub fn f_is_equal(cs: &mut Cs, x: &Field, y: &Field) -> Boolean {
    let r = f_is_not_equal(cs, x, y);
    b_not(&r)
}

/// helpers/zero.rs and helpers/one.rs.
pub fn f_is_zero(cs: &mut Cs, x: &Field) -> Boolean {
    f_is_equal(cs, x, &f_of(lc_zero()))
}

pub fn f_is_one(cs: &mut Cs, x: &Field) -> Boolean {
    f_is_equal(cs, x, &f_of(lc_one()))
}

/// ternary.rs: `(first - second) * (condition) = (output - second)`.
pub fn f_ternary(cs: &mut Cs, cond: &Boolean, first: &Field, second: &Field) -> Field {
    if b_is_const(cond) {
        if cond.k { f_copy(first) } else { f_copy(second) }
    } else if f_is_const(first) && f_is_const(second) {
        let nc = f_from_boolean(&b_not(cond));
        let c = f_from_boolean(cond);
        let l = f_mul(cs, &c, first);
        let r = f_mul(cs, &nc, second);
        f_add(&l, &r)
    } else {
        let out = f_new(cs);
        enforce(cs, lc_sub(&first.lc, &second.lc), lc_copy(&cond.lc), lc_sub(&out.lc, &second.lc));
        out
    }
}

/// helpers/to_bits.rs `to_non_unique_bits_le`: boolean bits and `assert_eq(self, sum 2^i b_i)`.
fn f_to_non_unique_bits_le(cs: &mut Cs, x: &Field) -> Vec<Boolean> {
    let mut bits = Vec::new();
    let mut i = 0;
    while i < FIELD_BITS {
        bits.push(b_new(cs));
        i += 1;
    }
    let mut acc = f_of(lc_zero());
    let mut coeff = f_of(lc_one());
    let mut j = 0;
    while j < bits.len() {
        let term = f_mul(cs, &f_from_boolean(&bits[j]), &coeff);
        acc = f_add(&acc, &term);
        coeff = f_add(&coeff, &coeff);
        j += 1;
    }
    env_assert_eq(cs, &x.lc, &acc.lc);
    bits
}

/// helpers/to_bits.rs `write_bits_le`. The bits are memoised in `bits_le`;
/// a caller that converts the same element twice stores them with `f_cache_bits`.
pub fn f_to_bits_le(cs: &mut Cs, x: &Field) -> Vec<Boolean> {
    match &x.bits {
        Bits::Some(b) => bits_copy(b),
        Bits::None => {
            let bits = f_to_non_unique_bits_le(cs, x);
            b_assert_less_than_or_equal_constant(cs, &bits, &p_minus_one_bits());
            bits
        }
    }
}

pub fn f_cache_bits(x: &Field, bits: &Vec<Boolean>) -> Field {
    Field { lc: lc_copy(&x.lc), bits: Bits::Some(bits_copy(bits)) }
}

pub fn f_to_bits_be(cs: &mut Cs, x: &Field) -> Vec<Boolean> {
    let le = f_to_bits_le(cs, x);
    bits_rev(&le)
}

/// helpers/from_bits.rs `from_bits_le`.
pub fn f_from_bits_le(cs: &mut Cs, bits: &Vec<Boolean>) -> Field {
    let n = bits.len();
    if n > FIELD_BITS {
        b_assert_bits_are_zero(cs, &bits_range(bits, FIELD_BITS, n));
    }
    if n > FIELD_DATA_BITS {
        b_assert_less_than_or_equal_constant(cs, &bits_range(bits, 0, FIELD_BITS), &p_minus_one_bits());
    }
    let mut out = f_of(lc_zero());
    let mut coeff = f_of(lc_one());
    let mut j = 0;
    while j < n && j < FIELD_BITS {
        let term = f_mul(cs, &f_from_boolean(&bits[j]), &coeff);
        out = f_add(&out, &term);
        coeff = f_add(&coeff, &coeff);
        j += 1;
    }
    let mut cached = bits_range(bits, 0, FIELD_BITS);
    while cached.len() < FIELD_BITS {
        cached.push(b_const(false));
    }
    out.bits = Bits::Some(cached);
    out
}

pub fn f_from_bits_be(cs: &mut Cs, bits: &Vec<Boolean>) -> Field {
    f_from_bits_le(cs, &bits_rev(bits))
}

/// compare.rs `is_less_than`, variable operands: ternary fold over the bits.
pub fn f_is_less_than(cs: &mut Cs, x: &Field, y: &Field) -> Boolean {
    let xb = f_to_bits_le(cs, x);
    let yb = f_to_bits_le(cs, y);
    let mut acc = b_const(false);
    let mut i = 0;
    while i < xb.len() && i < yb.len() {
        let d = b_xor(cs, &xb[i], &yb[i]);
        acc = b_ternary(cs, &d, &yb[i], &acc);
        i += 1;
    }
    acc
}

/// compare.rs `is_less_than` with a constant left operand, given by its bits.
pub fn f_const_is_less_than(cs: &mut Cs, kbits: &Vec<bool>, y: &Field) -> Boolean {
    let yb = f_to_bits_le(cs, y);
    let mut acc = b_const(false);
    let mut i = 0;
    while i < kbits.len() && i < yb.len() {
        acc = if kbits[i] { b_and(cs, &yb[i], &acc) } else { b_or(cs, &yb[i], &acc) };
        i += 1;
    }
    acc
}

/// compare.rs `is_less_than` with a constant right operand, given by its bits.
pub fn f_is_less_than_const(cs: &mut Cs, x: &Field, kbits: &Vec<bool>) -> Boolean {
    let xb = f_to_bits_le(cs, x);
    let mut acc = b_const(false);
    let mut i = 0;
    while i < kbits.len() && i < xb.len() {
        let nx = b_not(&xb[i]);
        acc = if kbits[i] { b_or(cs, &nx, &acc) } else { b_and(cs, &nx, &acc) };
        i += 1;
    }
    acc
}

pub fn f_is_greater_than(cs: &mut Cs, x: &Field, y: &Field) -> Boolean {
    f_is_less_than(cs, y, x)
}

pub fn f_is_greater_than_or_equal(cs: &mut Cs, x: &Field, y: &Field) -> Boolean {
    let r = f_is_less_than(cs, x, y);
    b_not(&r)
}

pub fn f_is_less_than_or_equal(cs: &mut Cs, x: &Field, y: &Field) -> Boolean {
    f_is_greater_than_or_equal(cs, y, x)
}

/// pow.rs, variable exponent: square, then a ternary on each big-endian bit.
pub fn f_pow(cs: &mut Cs, x: &Field, e: &Field) -> Field {
    let mut out = f_of(lc_one());
    let bits = f_to_bits_be(cs, e);
    let mut i = 0;
    while i < bits.len() {
        out = f_square(cs, &out);
        let prod = f_mul(cs, &out, x);
        out = f_ternary(cs, &bits[i], &prod, &out);
        i += 1;
    }
    out
}

/// square_root.rs `square_root`: `(r) * (r) = (self)` and `r <= (p - 1) / 2`.
pub fn f_square_root(cs: &mut Cs, x: &Field) -> Field {
    let r = f_new(cs);
    enforce(cs, lc_copy(&r.lc), lc_copy(&r.lc), lc_copy(&x.lc));
    // `r.is_less_than_or_equal(&half)` is `!half.is_less_than(r)`.
    let lt = f_const_is_less_than(cs, &p_half_bits(), &r);
    let lte = b_not(&lt);
    env_assert(cs, &lte.lc);
    r
}

/// square_root.rs `even_square_root`: the root and `assert(!lsb)`.
pub fn f_even_square_root(cs: &mut Cs, x: &Field) -> Field {
    let r = f_new(cs);
    enforce(cs, lc_copy(&r.lc), lc_copy(&r.lc), lc_copy(&x.lc));
    let be = f_to_bits_be(cs, &r);
    let lsb = b_not(&be[be.len() - 1]);
    env_assert(cs, &lsb.lc);
    r
}

/// helpers/to_lower_bits.rs `to_lower_bits_le`: `k` boolean witnesses and
/// `assert_eq(self, sum 2^i b_i)`.
pub fn f_to_lower_bits_le(cs: &mut Cs, x: &Field, k: usize) -> Vec<Boolean> {
    let mut bits = Vec::new();
    let mut i = 0;
    while i < k {
        bits.push(b_new(cs));
        i += 1;
    }
    let mut acc = f_of(lc_zero());
    let mut coeff = f_of(lc_one());
    let mut j = 0;
    while j < bits.len() {
        let term = f_mul(cs, &f_from_boolean(&bits[j]), &coeff);
        acc = f_add(&acc, &term);
        coeff = f_add(&coeff, &coeff);
        j += 1;
    }
    env_assert_eq(cs, &x.lc, &acc.lc);
    bits
}

/// helpers/to_upper_bits.rs `to_upper_bits_be`: `k` big-endian boolean
/// witnesses and `assert_eq(self, sum 2^(n-k+i) b_i)` over the reversed bits.
pub fn f_to_upper_bits_be(cs: &mut Cs, x: &Field, k: usize) -> Vec<Boolean> {
    let mut bits = Vec::new();
    let mut i = 0;
    while i < k {
        bits.push(b_new(cs));
        i += 1;
    }
    let mut coeff = f_of(lc_one());
    let mut s = 0;
    while s < FIELD_BITS - k {
        coeff = f_add(&coeff, &coeff);
        s += 1;
    }
    let le = bits_rev(&bits);
    let mut acc = f_of(lc_zero());
    let mut j = 0;
    while j < le.len() {
        let term = f_mul(cs, &f_from_boolean(&le[j]), &coeff);
        acc = f_add(&acc, &term);
        coeff = f_add(&coeff, &coeff);
        j += 1;
    }
    env_assert_eq(cs, &x.lc, &acc.lc);
    bits
}

/// div_unchecked.rs on two variables: a quotient witness and
/// `(quotient) * (other) = (self)`.
pub fn f_div_unchecked(cs: &mut Cs, x: &Field, y: &Field) -> Field {
    if f_is_const(y) || f_is_const(x) {
        let inv = f_inverse(cs, y);
        f_mul(cs, x, &inv)
    } else {
        let q = f_new(cs);
        enforce(cs, lc_copy(&q.lc), lc_copy(&y.lc), lc_copy(&x.lc));
        q
    }
}

/// Field bit helpers on a private input: 0 to_non_unique_bits_le,
/// 1 to_lower_bits_le(k), 2 to_upper_bits_be(k), 3 div_unchecked.
pub fn h_f_bits(op: u32, k: usize) -> Cs {
    let mut cs = cs_new();
    let x = f_new(&mut cs);
    if op == 0 {
        let _ = f_to_non_unique_bits_le(&mut cs, &x);
    } else if op == 1 {
        let _ = f_to_lower_bits_le(&mut cs, &x, k);
    } else if op == 2 {
        let _ = f_to_upper_bits_be(&mut cs, &x, k);
    } else {
        let y = f_new(&mut cs);
        let _ = f_div_unchecked(&mut cs, &x, &y);
    }
    cs
}

// ---------------------------------------------------------------------------
// circuit/types/integers. An integer is its little-endian bits; the width is
// their number.

pub struct Integer {
    pub bits: Vec<Boolean>,
    pub signed: bool,
}

fn i_copy(x: &Integer) -> Integer {
    Integer { bits: bits_copy(&x.bits), signed: x.signed }
}

fn i_width(x: &Integer) -> usize {
    x.bits.len()
}

fn i_is_const(x: &Integer) -> bool {
    let mut i = 0;
    let mut out = true;
    while i < x.bits.len() {
        if !b_is_const(&x.bits[i]) {
            out = false;
        }
        i += 1;
    }
    out
}

fn i_msb(x: &Integer) -> Boolean {
    b_copy(&x.bits[x.bits.len() - 1])
}

/// `Integer::constant` of the value whose two's-complement bits are `value`.
fn i_const_bits(value: &Vec<bool>, signed: bool) -> Integer {
    let mut bits = Vec::new();
    let mut i = 0;
    while i < value.len() {
        bits.push(b_const(value[i]));
        i += 1;
    }
    Integer { bits, signed }
}

fn i_const_small(n: usize, v: u32, signed: bool) -> Integer {
    let mut value = Vec::new();
    let mut i = 0;
    while i < n {
        value.push(i < 32 && (v >> (i as u32)) & 1 == 1);
        i += 1;
    }
    i_const_bits(&value, signed)
}

/// `I::MAX` (unsigned) and `-1` (signed) are both `n` one bits.
fn i_const_ones(n: usize, signed: bool) -> Integer {
    let mut value = Vec::new();
    let mut i = 0;
    while i < n {
        value.push(true);
        i += 1;
    }
    i_const_bits(&value, signed)
}

/// lib.rs `Integer::new(Mode::Private, _)`: one `Boolean::new` per bit.
pub fn i_new(cs: &mut Cs, n: usize, signed: bool) -> Integer {
    let mut bits = Vec::new();
    let mut i = 0;
    while i < n {
        bits.push(b_new(cs));
        i += 1;
    }
    Integer { bits, signed }
}

/// helpers/from_bits.rs `from_bits_le`: excess bits are asserted zero.
pub fn i_from_bits_le(cs: &mut Cs, bits: &Vec<Boolean>, n: usize, signed: bool) -> Integer {
    if bits.len() > n {
        b_assert_bits_are_zero(cs, &bits_range(bits, n, bits.len()));
    }
    let mut out = bits_range(bits, 0, n);
    while out.len() < n {
        out.push(b_const(false));
    }
    Integer { bits: out, signed }
}

pub fn i_from_bits_be(cs: &mut Cs, bits: &Vec<Boolean>, n: usize, signed: bool) -> Integer {
    i_from_bits_le(cs, &bits_rev(bits), n, signed)
}

/// helpers/to_field.rs: `Field::from_bits_le` of the bits.
pub fn i_to_field(cs: &mut Cs, x: &Integer) -> Field {
    f_from_bits_le(cs, &x.bits)
}

/// helpers/from_field.rs: `to_lower_bits_le(I::BITS)`.
pub fn i_from_field(cs: &mut Cs, f: &Field, n: usize, signed: bool) -> Integer {
    let bits = f_to_lower_bits_le(cs, f, n);
    Integer { bits, signed }
}

/// helpers/from_field_lossy.rs: the low bits of `to_bits_le`.
pub fn i_from_field_lossy(cs: &mut Cs, f: &Field, n: usize, signed: bool) -> Integer {
    let bits = f_to_bits_le(cs, f);
    Integer { bits: bits_range(&bits, 0, n), signed }
}

/// helpers/to_scalar.rs: `Scalar::from_bits_le` with fewer than the scalar
/// data bits, which is the bits' linear combination and no constraint.
pub fn i_to_scalar(cs: &mut Cs, x: &Integer) -> Field {
    f_from_bits_le(cs, &x.bits)
}

/// not.rs.
pub fn i_not(x: &Integer) -> Integer {
    let mut bits = Vec::new();
    let mut i = 0;
    while i < x.bits.len() {
        bits.push(b_not(&x.bits[i]));
        i += 1;
    }
    Integer { bits, signed: x.signed }
}

fn b_bitop(cs: &mut Cs, a: &Boolean, b: &Boolean, op: u32) -> Boolean {
    if op == 0 {
        b_and(cs, a, b)
    } else if op == 1 {
        b_or(cs, a, b)
    } else {
        b_xor(cs, a, b)
    }
}

/// and.rs, or.rs, xor.rs: bitwise. `op` is 0 AND, 1 OR, 2 XOR.
pub fn i_bitwise(cs: &mut Cs, x: &Integer, y: &Integer, op: u32) -> Integer {
    let xb = bits_copy(&x.bits);
    let yb = bits_copy(&y.bits);
    let mut bits = Vec::new();
    let mut i = 0;
    while i < xb.len() && i < yb.len() {
        bits.push(b_bitop(cs, &xb[i], &yb[i], op));
        i += 1;
    }
    Integer { bits, signed: x.signed }
}

fn i_ternary_var(cs: &mut Cs, cond: &Boolean, x: &Integer, y: &Integer) -> Integer {
    let xb = bits_copy(&x.bits);
    let yb = bits_copy(&y.bits);
    let mut bits = Vec::new();
    let mut i = 0;
    while i < xb.len() && i < yb.len() {
        bits.push(b_ternary(cs, cond, &xb[i], &yb[i]));
        i += 1;
    }
    Integer { bits, signed: x.signed }
}

/// ternary.rs: a Boolean ternary per bit.
pub fn i_ternary(cs: &mut Cs, cond: &Boolean, x: &Integer, y: &Integer) -> Integer {
    if b_is_const(cond) {
        if cond.k { i_copy(x) } else { i_copy(y) }
    } else {
        i_ternary_var(cs, cond, x, y)
    }
}

/// equal.rs: `to_field().is_equal(other.to_field())`.
pub fn i_is_equal(cs: &mut Cs, x: &Integer, y: &Integer) -> Boolean {
    if i_is_const(x) && i_is_const(y) {
        let mut acc = b_const(true);
        let mut i = 0;
        while i < x.bits.len() {
            let e = b_is_equal(cs, &x.bits[i], &y.bits[i]);
            acc = b_and(cs, &acc, &e);
            i += 1;
        }
        acc
    } else {
        let fx = i_to_field(cs, x);
        let fy = i_to_field(cs, y);
        f_is_equal(cs, &fx, &fy)
    }
}

pub fn i_is_not_equal(cs: &mut Cs, x: &Integer, y: &Integer) -> Boolean {
    let r = i_is_equal(cs, x, y);
    b_not(&r)
}

/// helpers/zero.rs and helpers/one.rs.
pub fn i_is_zero(cs: &mut Cs, x: &Integer) -> Boolean {
    let z = i_const_small(i_width(x), 0, x.signed);
    i_is_equal(cs, x, &z)
}

pub fn i_is_one(cs: &mut Cs, x: &Integer) -> Boolean {
    let o = i_const_small(i_width(x), 1, x.signed);
    i_is_equal(cs, x, &o)
}

fn f_plus_one(x: &Field) -> Field {
    f_add(x, &f_of(lc_one()))
}

fn i_value(x: &Integer) -> Vec<bool> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < x.bits.len() {
        out.push(x.bits[i].k);
        i += 1;
    }
    out
}

/// The low `x.len()` bits of `x + y + carry`.
fn bools_add(x: &Vec<bool>, y: &Vec<bool>, carry: bool) -> Vec<bool> {
    let mut out = Vec::new();
    let mut c = carry;
    let mut i = 0;
    while i < x.len() {
        let a = x[i];
        let b = i < y.len() && y[i];
        out.push(a != b && !c || a == b && c);
        c = a && b || a && c || b && c;
        i += 1;
    }
    out
}

fn bools_not(x: &Vec<bool>) -> Vec<bool> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < x.len() {
        out.push(!x[i]);
        i += 1;
    }
    out
}

/// `x << k`, truncated to the width of `x`.
fn bools_shl(x: &Vec<bool>, k: usize) -> Vec<bool> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < x.len() {
        out.push(i >= k && x[i - k]);
        i += 1;
    }
    out
}

/// The wrapping product of two equal-width values.
fn bools_mul(x: &Vec<bool>, y: &Vec<bool>) -> Vec<bool> {
    let mut acc = bools_shl(x, x.len());
    let mut i = 0;
    while i < y.len() {
        if y[i] {
            acc = bools_add(&acc, &bools_shl(x, i), false);
        }
        i += 1;
    }
    acc
}

/// add_wrapped.rs: the low `n` of `to_lower_bits_le(n + 1)` of the field sum.
pub fn i_add_wrapped(cs: &mut Cs, x: &Integer, y: &Integer) -> Integer {
    if i_is_const(x) && i_is_const(y) {
        return i_const_bits(&bools_add(&i_value(x), &i_value(y), false), x.signed);
    }
    let n = i_width(x);
    let fx = i_to_field(cs, x);
    let fy = i_to_field(cs, y);
    let sum = f_add(&fx, &fy);
    let bits = f_to_lower_bits_le(cs, &sum, n + 1);
    Integer { bits: bits_range(&bits, 0, n), signed: x.signed }
}

/// add_checked.rs `add_checked`.
pub fn i_add_checked(cs: &mut Cs, x: &Integer, y: &Integer) -> Integer {
    let n = i_width(x);
    if x.signed {
        let fx = i_to_field(cs, x);
        let fy = i_to_field(cs, y);
        let sum = f_add(&fx, &fy);
        let bits = f_to_lower_bits_le(cs, &sum, n + 1);
        let sum = i_from_bits_le(cs, &bits_range(&bits, 0, n), n, true);
        let is_same_sign = b_is_equal(cs, &i_msb(x), &i_msb(y));
        let neq = b_is_not_equal(cs, &i_msb(&sum), &i_msb(x));
        let is_overflow = b_and(cs, &is_same_sign, &neq);
        env_assert_eq(cs, &is_overflow.lc, &lc_zero());
        sum
    } else {
        let sum = i_new(cs, n, false);
        let fx = i_to_field(cs, x);
        let fy = i_to_field(cs, y);
        let computed = f_add(&fx, &fy);
        let witnessed = i_to_field(cs, &sum);
        env_assert_eq(cs, &computed.lc, &witnessed.lc);
        sum
    }
}

/// sub_wrapped.rs: `self + !other + 1`, low `n` bits.
pub fn i_sub_wrapped(cs: &mut Cs, x: &Integer, y: &Integer) -> Integer {
    if i_is_const(x) && i_is_const(y) {
        return i_const_bits(&bools_add(&i_value(x), &bools_not(&i_value(y)), true), x.signed);
    }
    let n = i_width(x);
    let fx = i_to_field(cs, x);
    let fny = i_to_field(cs, &i_not(y));
    let diff = f_plus_one(&f_add(&fx, &fny));
    let bits = f_to_lower_bits_le(cs, &diff, n + 1);
    Integer { bits: bits_range(&bits, 0, n), signed: x.signed }
}

/// sub_checked.rs `sub_checked`.
pub fn i_sub_checked(cs: &mut Cs, x: &Integer, y: &Integer) -> Integer {
    let n = i_width(x);
    let fx = i_to_field(cs, x);
    let fny = i_to_field(cs, &i_not(y));
    let diff = f_plus_one(&f_add(&fx, &fny));
    let bits = f_to_lower_bits_le(cs, &diff, n + 1);
    let carry = b_copy(&bits[n]);
    let difference = i_from_bits_le(cs, &bits_range(&bits, 0, n), n, x.signed);
    if x.signed {
        let is_different_signs = b_is_not_equal(cs, &i_msb(x), &i_msb(y));
        let eq = b_is_equal(cs, &i_msb(&difference), &i_msb(y));
        let is_underflow = b_and(cs, &is_different_signs, &eq);
        env_assert_eq(cs, &is_underflow.lc, &lc_zero());
    } else {
        env_assert_eq(cs, &carry.lc, &lc_one());
    }
    difference
}

/// abs_checked.rs and abs_wrapped.rs: `ternary(msb, 0 - self, self)` when signed.
pub fn i_abs(cs: &mut Cs, x: &Integer, checked: bool) -> Integer {
    if x.signed && i_is_const(x) {
        let v = i_value(x);
        if v[v.len() - 1] {
            i_const_bits(&bools_add(&bools_not(&v), &Vec::new(), true), true)
        } else {
            i_copy(x)
        }
    } else if x.signed {
        let zero = i_const_small(i_width(x), 0, true);
        let neg = if checked { i_sub_checked(cs, &zero, x) } else { i_sub_wrapped(cs, &zero, x) };
        i_ternary(cs, &i_msb(x), &neg, x)
    } else {
        i_copy(x)
    }
}

/// neg.rs, signed: `1.add_checked(!self)`.
pub fn i_neg(cs: &mut Cs, x: &Integer) -> Integer {
    let one = i_const_small(i_width(x), 1, true);
    i_add_checked(cs, &one, &i_not(x))
}

/// compare.rs `is_less_than`.
pub fn i_is_less_than(cs: &mut Cs, x: &Integer, y: &Integer) -> Boolean {
    let n = i_width(x);
    if x.signed {
        let same_sign = b_is_equal(cs, &i_msb(x), &i_msb(y));
        let nmy = b_not(&i_msb(y));
        let neg_pos = b_and(cs, &i_msb(x), &nmy);
        let m1 = i_to_field(cs, &i_const_ones(n, true));
        let fx = i_to_field(cs, x);
        let fy = i_to_field(cs, y);
        let e = f_plus_one(&f_sub(&f_add(&m1, &fx), &fy));
        let bits = f_to_lower_bits_le(cs, &e, n + 1);
        let nb = b_not(&bits[n]);
        b_ternary(cs, &same_sign, &nb, &neg_pos)
    } else {
        let max = i_to_field(cs, &i_const_ones(n, false));
        let fx = i_to_field(cs, x);
        let fy = i_to_field(cs, y);
        let e = f_plus_one(&f_sub(&f_add(&max, &fx), &fy));
        let bits = f_to_lower_bits_le(cs, &e, n + 1);
        b_not(&bits[n])
    }
}

fn f_bits_range(cs: &mut Cs, bits: &Vec<Boolean>, lo: usize, hi: usize) -> Field {
    f_from_bits_le(cs, &bits_range(bits, lo, hi))
}

/// `Field::from_bits_le` of `h` zero bits and a one bit: the constant 2^h.
fn f_pow2(cs: &mut Cs, h: usize) -> Field {
    let mut bits = Vec::new();
    let mut i = 0;
    while i < h {
        bits.push(b_const(false));
        i += 1;
    }
    bits.push(b_const(true));
    f_from_bits_le(cs, &bits)
}

/// mul_wrapped.rs `mul_wrapped`.
pub fn i_mul_wrapped(cs: &mut Cs, x: &Integer, y: &Integer) -> Integer {
    if i_is_const(x) && i_is_const(y) {
        return i_const_bits(&bools_mul(&i_value(x), &i_value(y)), x.signed);
    }
    let n = i_width(x);
    let h = n / 2;
    let x1 = f_bits_range(cs, &x.bits, h, n);
    let x0 = f_bits_range(cs, &x.bits, 0, h);
    let y1 = f_bits_range(cs, &y.bits, h, n);
    let y0 = f_bits_range(cs, &y.bits, 0, h);
    let z0 = f_mul(cs, &x0, &y0);
    let a = f_mul(cs, &x1, &y0);
    let b = f_mul(cs, &x0, &y1);
    let z1 = f_add(&a, &b);
    let bm = f_pow2(cs, h);
    let scaled = f_mul(cs, &z1, &bm);
    let sum = f_add(&z0, &scaled);
    let bits = f_to_lower_bits_le(cs, &sum, n + h + 1);
    Integer { bits: bits_range(&bits, 0, n), signed: x.signed }
}

pub struct Karatsuba {
    pub product: Integer,
    pub carry: Vec<Boolean>,
    pub z2: Field,
}

/// mul_checked.rs `karatsuba_multiply`.
pub fn i_karatsuba_multiply(cs: &mut Cs, x: &Integer, y: &Integer) -> Karatsuba {
    let n = i_width(x);
    let h = n / 2;
    let x1 = f_bits_range(cs, &x.bits, h, n);
    let x0 = f_bits_range(cs, &x.bits, 0, h);
    let y1 = f_bits_range(cs, &y.bits, h, n);
    let y0 = f_bits_range(cs, &y.bits, 0, h);
    let z0 = f_mul(cs, &x0, &y0);
    let z2 = f_mul(cs, &x1, &y1);
    let m = f_mul(cs, &f_add(&x1, &x0), &f_add(&y1, &y0));
    let z1 = f_sub(&f_sub(&m, &z2), &z0);
    let bm = f_pow2(cs, h);
    let scaled = f_mul(cs, &z1, &bm);
    let sum = f_add(&z0, &scaled);
    let bits = f_to_lower_bits_le(cs, &sum, n + h + 1);
    let product = i_from_bits_le(cs, &bits_range(&bits, 0, n), n, x.signed);
    Karatsuba { product, carry: bits_range(&bits, n, bits.len()), z2 }
}

/// mul_checked.rs `mul_and_check`.
pub fn i_mul_and_check(cs: &mut Cs, x: &Integer, y: &Integer) -> Integer {
    let n = i_width(x);
    if 2 * n < FIELD_BITS - 1 {
        let product = i_new(cs, n, x.signed);
        let fx = i_to_field(cs, x);
        let fy = i_to_field(cs, y);
        let fp = i_to_field(cs, &product);
        enforce(cs, fx.lc, fy.lc, fp.lc);
        product
    } else {
        let k = i_karatsuba_multiply(cs, x, y);
        b_assert_bits_are_zero(cs, &k.carry);
        env_assert_eq(cs, &k.z2.lc, &lc_zero());
        k.product
    }
}

fn b_or_fold(cs: &mut Cs, bits: &Vec<Boolean>) -> Boolean {
    let local = bits_copy(bits);
    let mut acc = b_const(false);
    let mut i = 0;
    while i < local.len() {
        acc = b_or(cs, &acc, &local[i]);
        i += 1;
    }
    acc
}

/// mul_checked.rs `mul_checked`.
/// A constant product that overflows halts in snarkVM; it is not modelled.
pub fn i_mul_checked(cs: &mut Cs, x: &Integer, y: &Integer) -> Integer {
    if i_is_const(x) && i_is_const(y) {
        i_const_bits(&bools_mul(&i_value(x), &i_value(y)), x.signed)
    } else if x.signed {
        let n = i_width(x);
        let ax = i_abs(cs, x, false);
        let ay = i_abs(cs, y, false);
        let product = i_mul_and_check(cs, &ax, &ay);
        let same_sign = b_is_equal(cs, &i_msb(x), &i_msb(y));
        let pos_overflow = b_and(cs, &same_sign, &i_msb(&product));
        env_assert_eq(cs, &pos_overflow.lc, &lc_zero());
        let lower_nonzero = b_or_fold(cs, &bits_range(&product.bits, 0, n - 1));
        let nmsb = b_not(&i_msb(&product));
        let nlower = b_not(&lower_nonzero);
        let msb_and = b_and(cs, &i_msb(&product), &nlower);
        let lte_min = b_or(cs, &nmsb, &msb_and);
        let nsame = b_not(&same_sign);
        let nlte = b_not(&lte_min);
        let neg_underflow = b_and(cs, &nsame, &nlte);
        env_assert_eq(cs, &neg_underflow.lc, &lc_zero());
        let zero = i_const_small(n, 0, true);
        let negp = i_sub_wrapped(cs, &zero, &product);
        i_ternary(cs, &same_sign, &product, &negp)
    } else {
        i_mul_and_check(cs, x, y)
    }
}

pub struct ProductFlag {
    pub product: Integer,
    pub flag: Boolean,
}

/// pow_checked.rs `mul_with_flags`.
fn i_mul_with_flags(cs: &mut Cs, x: &Integer, y: &Integer) -> ProductFlag {
    let n = i_width(x);
    if 2 * n < FIELD_BITS - 1 {
        let product = i_new(cs, n, x.signed);
        let fx = i_to_field(cs, x);
        let fy = i_to_field(cs, y);
        let computed = f_mul(cs, &fx, &fy);
        let witnessed = i_to_field(cs, &product);
        let flag = f_is_not_equal(cs, &computed, &witnessed);
        ProductFlag { product, flag }
    } else {
        let k = i_karatsuba_multiply(cs, x, y);
        let upper = f_from_bits_le(cs, &k.carry);
        let sum = f_add(&upper, &k.z2);
        let flag = f_is_not_equal(cs, &sum, &f_of(lc_zero()));
        ProductFlag { product: k.product, flag }
    }
}

/// pow_wrapped.rs, variable operands: from the most significant exponent bit,
/// square, then multiply when the bit is set.
pub fn i_pow_wrapped(cs: &mut Cs, x: &Integer, e: &Integer) -> Integer {
    let one = i_const_small(i_width(x), 1, x.signed);
    let bits = bits_rev(&e.bits);
    i_pow_wrapped_from(cs, x, &bits, 0, one)
}

fn i_pow_wrapped_from(cs: &mut Cs, x: &Integer, bits: &Vec<Boolean>, i: usize, result: Integer) -> Integer {
    if i < bits.len() {
        let sq = i_mul_wrapped(cs, &result, &result);
        let prod = i_mul_wrapped(cs, &sq, x);
        let next = i_ternary(cs, &bits[i], &prod, &sq);
        i_pow_wrapped_from(cs, x, bits, i + 1, next)
    } else {
        result
    }
}

/// pow_checked.rs, variable operands.
pub fn i_pow_checked(cs: &mut Cs, x: &Integer, e: &Integer) -> Integer {
    let one = i_const_small(i_width(x), 1, x.signed);
    let bits = bits_rev(&e.bits);
    i_pow_checked_from(cs, x, &bits, 0, one)
}

fn i_pow_checked_times(cs: &mut Cs, result: &Integer, x: &Integer, bit: &Boolean) -> Integer {
    if x.signed {
        let n = i_width(x);
        let ar = i_abs(cs, result, false);
        let ax = i_abs(cs, x, false);
        let pf = i_mul_with_flags(cs, &ar, &ax);
        let product = pf.product;
        let same_sign = b_is_equal(cs, &i_msb(result), &i_msb(x));
        let pos_overflow = b_and(cs, &same_sign, &i_msb(&product));
        let lower_nonzero = b_or_fold(cs, &bits_range(&product.bits, 0, n - 1));
        let nmsb = b_not(&i_msb(&product));
        let nlower = b_not(&lower_nonzero);
        let msb_and = b_and(cs, &i_msb(&product), &nlower);
        let lte_min = b_or(cs, &nmsb, &msb_and);
        let nsame = b_not(&same_sign);
        let nlte = b_not(&lte_min);
        let neg_underflow = b_and(cs, &nsame, &nlte);
        let o1 = b_or(cs, &pf.flag, &pos_overflow);
        let overflow = b_or(cs, &o1, &neg_underflow);
        let check = b_and(cs, &overflow, bit);
        env_assert_eq(cs, &check.lc, &lc_zero());
        let one = i_const_small(n, 1, true);
        let negp = i_add_wrapped(cs, &i_not(&product), &one);
        i_ternary(cs, &same_sign, &product, &negp)
    } else {
        let pf = i_mul_with_flags(cs, result, x);
        let check = b_and(cs, &pf.flag, bit);
        env_assert_eq(cs, &check.lc, &lc_zero());
        pf.product
    }
}

fn i_pow_checked_from(cs: &mut Cs, x: &Integer, bits: &Vec<Boolean>, i: usize, result: Integer) -> Integer {
    if i < bits.len() {
        let sq = i_mul_checked(cs, &result, &result);
        let times = i_pow_checked_times(cs, &sq, x, &bits[i]);
        let next = i_ternary(cs, &bits[i], &times, &sq);
        i_pow_checked_from(cs, x, bits, i + 1, next)
    } else {
        result
    }
}

/// modulo.rs: `rem_wrapped` (unsigned only).
pub fn i_modulo(cs: &mut Cs, x: &Integer, y: &Integer) -> Integer {
    i_div_rem(cs, x, y, false, true)
}

pub struct DivRem {
    pub q: Integer,
    pub r: Integer,
}

/// div_wrapped.rs `unsigned_division_via_witness`.
pub fn i_unsigned_division_via_witness(cs: &mut Cs, x: &Integer, y: &Integer) -> DivRem {
    let n = i_width(x);
    let q = i_new(cs, n, false);
    let r = i_new(cs, n, false);
    if 2 * n < FIELD_DATA_BITS {
        let fx = i_to_field(cs, x);
        let fq = i_to_field(cs, &q);
        let fy = i_to_field(cs, y);
        let fr = i_to_field(cs, &r);
        let qy = f_mul(cs, &fq, &fy);
        env_assert_eq(cs, &fx.lc, &f_add(&qy, &fr).lc);
    } else {
        let qy = i_mul_checked(cs, &q, y);
        let t = i_add_checked(cs, &qy, &r);
        let fx = i_to_field(cs, x);
        let ft = i_to_field(cs, &t);
        env_assert_eq(cs, &fx.lc, &ft.lc);
    }
    let lt = i_is_less_than(cs, &r, y);
    env_assert(cs, &lt.lc);
    DivRem { q, r }
}

fn i_as_unsigned(x: &Integer) -> Integer {
    Integer { bits: bits_copy(&x.bits), signed: false }
}

fn i_as_signed(x: &Integer) -> Integer {
    Integer { bits: bits_copy(&x.bits), signed: true }
}

/// The signed overflow check of div_checked.rs and rem_checked.rs:
/// `assert(!(self == MIN & other == -1))`.
fn i_assert_not_min_div_neg_one(cs: &mut Cs, x: &Integer, y: &Integer) {
    let n = i_width(x);
    let mut minbits = Vec::new();
    let mut i = 0;
    while i < n {
        minbits.push(i == n - 1);
        i += 1;
    }
    let min = i_const_bits(&minbits, true);
    let neg_one = i_const_ones(n, true);
    let a = i_is_equal(cs, x, &min);
    let b = i_is_equal(cs, y, &neg_one);
    let overflows = b_and(cs, &a, &b);
    env_assert(cs, &b_not(&overflows).lc);
}

/// div_wrapped.rs and div_checked.rs (`checked` adds the overflow check);
/// `rem` selects rem_wrapped.rs and rem_checked.rs.
pub fn i_div_rem(cs: &mut Cs, x: &Integer, y: &Integer, checked: bool, rem: bool) -> Integer {
    if x.signed {
        if checked {
            i_assert_not_min_div_neg_one(cs, x, y);
        }
        let ax = i_as_unsigned(&i_abs(cs, x, false));
        let ay = i_as_unsigned(&i_abs(cs, y, false));
        let dr = i_unsigned_division_via_witness(cs, &ax, &ay);
        let n = i_width(x);
        let zero = i_const_small(n, 0, true);
        if rem {
            let sr = i_as_signed(&dr.r);
            let neg = i_sub_wrapped(cs, &zero, &sr);
            let c = b_not(&i_msb(x));
            i_ternary(cs, &c, &sr, &neg)
        } else {
            let sq = i_as_signed(&dr.q);
            let same = b_is_equal(cs, &i_msb(x), &i_msb(y));
            let neg = i_sub_wrapped(cs, &zero, &sq);
            i_ternary(cs, &same, &sq, &neg)
        }
    } else {
        let dr = i_unsigned_division_via_witness(cs, x, y);
        if rem { dr.r } else { dr.q }
    }
}

fn log2_width(n: usize) -> usize {
    let mut k = 0;
    while (1usize << k) < n && k < 8 {
        k += 1;
    }
    k
}

/// The select chain of the field shifts: for each low exponent bit i, the
/// running value times 2^(2^i) if the bit is set; `msb`, if given, adds the
/// sign-extension mask (2^(2^i) - 1) * msb.
fn shift_chain(cs: &mut Cs, start: &Field, ebits: &Vec<Boolean>, msb: &Bits) -> Field {
    let local = bits_copy(ebits);
    let mut result = f_copy(start);
    let mut i = 0;
    while i < local.len() {
        let product = f_mul(cs, &result, &f_of(lc_const(1, 1u32 << (i as u32))));
        let next = match msb {
            Bits::Some(m) => {
                let mask = f_of(lc_sub(&lc_const(1, 1u32 << (i as u32)), &lc_one()));
                let mf = f_from_boolean(&m[0]);
                let masked = f_add(&product, &f_mul(cs, &mask, &mf));
                f_ternary(cs, &local[i], &masked, &result)
            }
            Bits::None => f_ternary(cs, &local[i], &product, &result),
        };
        result = next;
        i += 1;
    }
    result
}

/// The 128-bit shifts: 2^e for the low exponent bits by square-and-select,
/// as an integer of width n.
fn shift_power(cs: &mut Cs, ebits: &Vec<Boolean>, n: usize) -> Integer {
    let local = bits_rev(ebits);
    let two = f_of(lc_const(2, 0));
    let mut shift = f_of(lc_one());
    let mut i = 0;
    while i < local.len() {
        let sq = f_square(cs, &shift);
        let dbl = f_mul(cs, &sq, &two);
        shift = f_ternary(cs, &local[i], &dbl, &sq);
        i += 1;
    }
    Integer { bits: f_to_lower_bits_le(cs, &shift, n), signed: false }
}

/// shl_wrapped.rs; `rhs` is the shift amount of any magnitude width.
pub fn i_shl_wrapped(cs: &mut Cs, x: &Integer, rhs: &Integer) -> Integer {
    let n = i_width(x);
    let ebits = bits_range(&rhs.bits, 0, log2_width(n));
    if 2 * n < FIELD_DATA_BITS {
        let start = i_to_field(cs, x);
        let r = shift_chain(cs, &start, &ebits, &Bits::None);
        let bits = f_to_lower_bits_le(cs, &r, 2 * n);
        Integer { bits: bits_range(&bits, 0, n), signed: x.signed }
    } else {
        let s = shift_power(cs, &ebits, n);
        let factor = Integer { bits: s.bits, signed: x.signed };
        i_mul_wrapped(cs, x, &factor)
    }
}

/// shl_checked.rs, widths 8 to 64.
pub fn i_shl_checked(cs: &mut Cs, x: &Integer, rhs: &Integer) -> Integer {
    let n = i_width(x);
    let k = log2_width(n);
    let ebits = bits_range(&rhs.bits, 0, k);
    b_assert_bits_are_zero(cs, &bits_range(&rhs.bits, k, rhs.bits.len()));
    if x.signed {
        let mut ext = bits_copy(&x.bits);
        while ext.len() < 2 * n {
            ext.push(i_msb(x));
        }
        let start = f_from_bits_le(cs, &ext);
        let r = shift_chain(cs, &start, &ebits, &Bits::None);
        let bits = f_to_lower_bits_le(cs, &r, 3 * n);
        let result = Integer { bits: bits_range(&bits, 0, n), signed: true };
        let upper = bits_range(&bits, n, 2 * n);
        let msb = i_msb(&result);
        let mut j = 0;
        while j < upper.len() {
            env_assert_eq(cs, &upper[j].lc, &msb.lc);
            j += 1;
        }
        result
    } else {
        let start = i_to_field(cs, x);
        let r = shift_chain(cs, &start, &ebits, &Bits::None);
        let bits = f_to_lower_bits_le(cs, &r, 2 * n);
        b_assert_bits_are_zero(cs, &bits_range(&bits, n, 2 * n));
        Integer { bits: bits_range(&bits, 0, n), signed: false }
    }
}

/// shr_wrapped.rs.
pub fn i_shr_wrapped(cs: &mut Cs, x: &Integer, rhs: &Integer) -> Integer {
    let n = i_width(x);
    let ebits = bits_range(&rhs.bits, 0, log2_width(n));
    if 2 * n < FIELD_DATA_BITS {
        let start = f_from_bits_be(cs, &x.bits);
        let msb = if x.signed {
            let mut m = Vec::new();
            m.push(i_msb(x));
            Bits::Some(m)
        } else {
            Bits::None
        };
        let r = shift_chain(cs, &start, &ebits, &msb);
        let bits = f_to_lower_bits_le(cs, &r, 2 * n);
        Integer { bits: bits_rev(&bits_range(&bits, 0, n)), signed: x.signed }
    } else {
        let divisor = shift_power(cs, &ebits, n);
        if x.signed {
            let ax = i_as_unsigned(&i_abs(cs, x, false));
            let dr = i_unsigned_division_via_witness(cs, &ax, &divisor);
            let q = i_as_signed(&dr.q);
            let one = i_const_small(n, 1, true);
            let nq = i_add_wrapped(cs, &i_not(&q), &one);
            let fr = i_to_field(cs, &dr.r);
            let rz = f_is_equal(cs, &fr, &f_of(lc_zero()));
            let nq1 = i_sub_wrapped(cs, &nq, &one);
            let rounded = i_ternary(cs, &rz, &nq, &nq1);
            i_ternary(cs, &i_msb(x), &rounded, &q)
        } else {
            i_unsigned_division_via_witness(cs, x, &divisor).q
        }
    }
}

/// shr_checked.rs.
pub fn i_shr_checked(cs: &mut Cs, x: &Integer, rhs: &Integer) -> Integer {
    let k = log2_width(i_width(x));
    b_assert_bits_are_zero(cs, &bits_range(&rhs.bits, k, rhs.bits.len()));
    i_shr_wrapped(cs, x, rhs)
}

/// `op`: 0 is_less_than, 1 is_greater_than, 2 is_less_than_or_equal,
/// 3 is_greater_than_or_equal.
pub fn i_compare(cs: &mut Cs, x: &Integer, y: &Integer, op: u32) -> Boolean {
    if op == 0 {
        i_is_less_than(cs, x, y)
    } else if op == 1 {
        i_is_less_than(cs, y, x)
    } else if op == 2 {
        let r = i_is_less_than(cs, y, x);
        b_not(&r)
    } else {
        let r = i_is_less_than(cs, x, y);
        b_not(&r)
    }
}

// ---------------------------------------------------------------------------
// circuit/types/scalar

/// The constant field element with little-endian bits `k`.
fn f_const_bits(k: &Vec<bool>) -> Field {
    let mut lc = lc_zero();
    let mut i = 0;
    while i < k.len() {
        if k[i] {
            lc = lc_add(&lc, &lc_const(1, i as u32));
        }
        i += 1;
    }
    f_of(lc)
}

/// lib.rs `Scalar::new(Mode::Private, _)`: a field witness, no constraint.
pub fn s_new(cs: &mut Cs) -> Field {
    f_new(cs)
}

/// helpers/to_bits.rs `write_bits_le`: to_lower_bits_le(251) and
/// `assert_less_than_or_equal_constant` against r - 1.
pub fn s_to_bits_le(cs: &mut Cs, x: &Field) -> Vec<Boolean> {
    let bits = f_to_lower_bits_le(cs, x, SCALAR_BITS);
    b_assert_less_than_or_equal_constant(cs, &bits, &limbs_bits(&R_MINUS_ONE, SCALAR_BITS));
    bits
}

/// compare.rs `is_less_than`: the low bit of `to_bits_le` of 2(x - y).
pub fn s_is_less_than(cs: &mut Cs, x: &Field, y: &Field) -> Boolean {
    let d = f_sub(x, y);
    let outcome = f_add(&d, &d);
    let bits = f_to_bits_le(cs, &outcome);
    b_copy(&bits[0])
}

/// `op`: 0 is_less_than, 1 is_greater_than, 2 is_less_than_or_equal,
/// 3 is_greater_than_or_equal.
pub fn s_compare(cs: &mut Cs, x: &Field, y: &Field, op: u32) -> Boolean {
    if op == 0 {
        s_is_less_than(cs, x, y)
    } else if op == 1 {
        s_is_less_than(cs, y, x)
    } else if op == 2 {
        let r = s_is_less_than(cs, y, x);
        b_not(&r)
    } else {
        let r = s_is_less_than(cs, x, y);
        b_not(&r)
    }
}

/// add.rs `add_assign`.
pub fn s_add(cs: &mut Cs, x: &Field, y: &Field) -> Field {
    let sum = f_add(x, y);
    let bits = f_to_lower_bits_le(cs, &sum, SCALAR_BITS + 1);
    let sumf = f_from_bits_le(cs, &bits);
    let rbits = limbs_bits(&R, FIELD_BITS);
    let modulus = f_const_bits(&rbits);
    let lt = f_is_less_than_const(cs, &sumf, &rbits);
    let wrapping = f_ternary(cs, &lt, &sumf, &f_sub(&sumf, &modulus));
    let _ = f_to_lower_bits_le(cs, &wrapping, SCALAR_BITS);
    wrapping
}

/// helpers/from_bits.rs `from_bits_le`.
pub fn s_from_bits_le(cs: &mut Cs, bits: &Vec<Boolean>) -> Field {
    let n = bits.len();
    if n > SCALAR_BITS {
        b_assert_bits_are_zero(cs, &bits_range(bits, SCALAR_BITS, n));
    }
    if n > SCALAR_DATA_BITS {
        let low = bits_range(bits, 0, SCALAR_BITS);
        let f = f_from_bits_le(cs, &low);
        b_assert_less_than_or_equal_constant(cs, &low, &limbs_bits(&R_MINUS_ONE, SCALAR_BITS));
        f
    } else {
        f_from_bits_le(cs, bits)
    }
}

// ---------------------------------------------------------------------------
// circuit/types/group. Edwards BLS12: a = -1 and d = 3021.

pub struct Group {
    pub x: Field,
    pub y: Field,
}

const EDWARDS_A: i128 = -1;
const EDWARDS_D: i128 = 3021;

fn g_copy(g: &Group) -> Group {
    Group { x: f_copy(&g.x), y: f_copy(&g.y) }
}

/// helpers/zero.rs `Group::zero()`: the constant (0, 1).
pub fn g_zero() -> Group {
    Group { x: f_of(lc_zero()), y: f_of(lc_one()) }
}

fn lc_is_zero(x: &Vec<Term>) -> bool {
    x.len() == 0
}

fn lc_is_one(x: &Vec<Term>) -> bool {
    x.len() == 1 && x[0].v == 0 && x[0].c == 1 && x[0].sh == 0 && x[0].k == 0
}

/// `self.is_constant() && self.eject_value().is_zero()`.
fn g_is_const_zero(g: &Group) -> bool {
    lc_is_zero(&g.x.lc) && lc_is_one(&g.y.lc)
}

fn g_is_const(g: &Group) -> bool {
    f_is_const(&g.x) && f_is_const(&g.y)
}

/// neg.rs: `(-x, y)`.
pub fn g_neg(g: &Group) -> Group {
    Group { x: f_of(lc_neg(&g.x.lc)), y: f_copy(&g.y) }
}

/// add.rs `add`.
pub fn g_add(cs: &mut Cs, s: &Group, o: &Group) -> Group {
    if g_is_const_zero(s) {
        g_copy(o)
    } else if g_is_const_zero(o) {
        g_copy(s)
    } else {
        let this = if g_is_const(o) { g_copy(s) } else { g_copy(o) };
        let that = if g_is_const(o) { g_copy(o) } else { g_copy(s) };
        let a = f_of(lc_const(EDWARDS_A, 0));
        let d = f_of(lc_const(EDWARDS_D, 0));
        let neg_a = f_of(lc_neg(&a.lc));
        let u1x = f_mul(cs, &this.x, &neg_a);
        let u1 = f_add(&u1x, &this.y);
        let u2 = f_add(&that.x, &that.y);
        let u = f_mul(cs, &u1, &u2);
        let v0 = f_mul(cs, &this.x, &that.y);
        let v1 = f_mul(cs, &that.x, &this.y);
        let v01 = f_mul(cs, &v0, &v1);
        let v2 = f_mul(cs, &v01, &d);
        let x3 = f_new(cs);
        let y3 = f_new(cs);
        let v2_plus_one = f_add(&v2, &f_of(lc_one()));
        let v0_plus_v1 = f_add(&v0, &v1);
        enforce(cs, lc_copy(&x3.lc), v2_plus_one.lc, v0_plus_v1.lc);
        let one_minus_v2 = f_sub(&f_of(lc_one()), &v2);
        let a_v0 = f_mul(cs, &v0, &a);
        let rhs = f_sub(&f_add(&u, &a_v0), &v1);
        enforce(cs, lc_copy(&y3.lc), one_minus_v2.lc, rhs.lc);
        Group { x: x3, y: y3 }
    }
}

/// sub.rs: `self + -other`.
pub fn g_sub(cs: &mut Cs, s: &Group, o: &Group) -> Group {
    let n = g_neg(o);
    g_add(cs, s, &n)
}

struct DoubleTerms {
    ax2_plus_y2: Field,
    two_xy: Field,
    two_minus: Field,
    y2_minus_ax2: Field,
}

/// The products shared by `double` and `enforce_double`.
fn g_double_terms(cs: &mut Cs, g: &Group) -> DoubleTerms {
    let a = f_of(lc_const(EDWARDS_A, 0));
    let two = f_of(lc_const(2, 0));
    let xy = f_mul(cs, &g.x, &g.y);
    let x2 = f_square(cs, &g.x);
    let y2 = f_square(cs, &g.y);
    let ax2 = f_mul(cs, &x2, &a);
    let ax2_plus_y2 = f_add(&ax2, &y2);
    let two_xy = f_add(&xy, &xy);
    let y2_minus_ax2 = f_sub(&y2, &ax2);
    let two_minus = f_sub(&two, &ax2_plus_y2);
    DoubleTerms { ax2_plus_y2, two_xy, two_minus, y2_minus_ax2 }
}

/// double.rs `double`.
pub fn g_double(cs: &mut Cs, g: &Group) -> Group {
    if g_is_const_zero(g) {
        g_copy(g)
    } else {
        let t = g_double_terms(cs, g);
        let x3 = f_new(cs);
        let y3 = f_new(cs);
        enforce(cs, lc_copy(&x3.lc), t.ax2_plus_y2.lc, t.two_xy.lc);
        enforce(cs, lc_copy(&y3.lc), t.two_minus.lc, t.y2_minus_ax2.lc);
        Group { x: x3, y: y3 }
    }
}

/// double.rs `enforce_double`.
pub fn g_enforce_double(cs: &mut Cs, g: &Group, dbl: &Group) {
    let t = g_double_terms(cs, g);
    enforce(cs, lc_copy(&dbl.x.lc), t.ax2_plus_y2.lc, t.two_xy.lc);
    enforce(cs, lc_copy(&dbl.y.lc), t.two_minus.lc, t.y2_minus_ax2.lc);
}

/// helpers/mul_by_cofactor.rs: two doublings.
pub fn g_mul_by_cofactor(cs: &mut Cs, g: &Group) -> Group {
    let d = g_double(cs, g);
    g_double(cs, &d)
}

/// lib.rs `enforce_on_curve`: `(y^2) * (d x^2 - 1) = (a x^2 - 1)`.
pub fn g_enforce_on_curve(cs: &mut Cs, g: &Group) {
    let a = f_of(lc_const(EDWARDS_A, 0));
    let d = f_of(lc_const(EDWARDS_D, 0));
    let x2 = f_square(cs, &g.x);
    let y2 = f_square(cs, &g.y);
    let dx2 = f_mul(cs, &d, &x2);
    let second = f_sub(&dx2, &f_of(lc_one()));
    let ax2 = f_mul(cs, &a, &x2);
    let third = f_sub(&ax2, &f_of(lc_one()));
    enforce(cs, y2.lc, second.lc, third.lc);
}

/// lib.rs `enforce_in_group`: a witnessed point whose double is `self`.
pub fn g_enforce_in_group(cs: &mut Cs, g: &Group) {
    let point = if g_is_const(g) { g_zero() } else { g_witness(cs) };
    g_enforce_on_curve(cs, &point);
    let dbl = g_double(cs, &point);
    g_enforce_double(cs, &dbl, g);
}

fn g_witness(cs: &mut Cs) -> Group {
    let x = f_new(cs);
    let y = f_new(cs);
    Group { x, y }
}

/// lib.rs `Group::new(Mode::Private, _)`.
pub fn g_new(cs: &mut Cs) -> Group {
    let g = g_witness(cs);
    g_enforce_in_group(cs, &g);
    g
}

/// helpers/from_xy_coordinates.rs.
pub fn g_from_xy_coordinates(cs: &mut Cs, x: &Field, y: &Field) -> Group {
    let g = Group { x: f_copy(x), y: f_copy(y) };
    g_enforce_in_group(cs, &g);
    g
}

/// helpers/from_x_coordinate.rs: a witnessed y.
pub fn g_from_x_coordinate(cs: &mut Cs, x: &Field) -> Group {
    let y = if f_is_const(x) { f_of(lc_zero()) } else { f_new(cs) };
    g_from_xy_coordinates(cs, x, &y)
}

/// helpers/from_bits.rs.
pub fn g_from_bits_le(cs: &mut Cs, bits: &Vec<Boolean>) -> Group {
    let x = f_from_bits_le(cs, bits);
    g_from_x_coordinate(cs, &x)
}

pub fn g_from_bits_be(cs: &mut Cs, bits: &Vec<Boolean>) -> Group {
    let x = f_from_bits_be(cs, bits);
    g_from_x_coordinate(cs, &x)
}

/// equal.rs.
pub fn g_is_equal(cs: &mut Cs, s: &Group, o: &Group) -> Boolean {
    let ex = f_is_equal(cs, &s.x, &o.x);
    let ey = f_is_equal(cs, &s.y, &o.y);
    b_and(cs, &ex, &ey)
}

pub fn g_is_not_equal(cs: &mut Cs, s: &Group, o: &Group) -> Boolean {
    let r = g_is_equal(cs, s, o);
    b_not(&r)
}

/// helpers/zero.rs `is_zero`.
pub fn g_is_zero(cs: &mut Cs, g: &Group) -> Boolean {
    let ex = f_is_equal(cs, &g.x, &f_of(lc_zero()));
    let ey = f_is_equal(cs, &g.y, &f_of(lc_one()));
    b_and(cs, &ex, &ey)
}

/// ternary.rs.
pub fn g_ternary(cs: &mut Cs, c: &Boolean, first: &Group, second: &Group) -> Group {
    let x = f_ternary(cs, c, &first.x, &second.x);
    let y = f_ternary(cs, c, &first.y, &second.y);
    Group { x, y }
}

/// helpers/to_bits.rs: the bits of x.
pub fn g_to_bits_le(cs: &mut Cs, g: &Group) -> Vec<Boolean> {
    f_to_bits_le(cs, &g.x)
}

fn g_mul_step(cs: &mut Cs, bit: &Boolean, base: &Group, output: &Group) -> Group {
    let dbl = g_double(cs, output);
    let sum = g_add(cs, base, &dbl);
    g_ternary(cs, bit, &sum, &dbl)
}

/// mul.rs `mul_assign` by big-endian bits: double-and-add from zero.
pub fn g_mul_bits(cs: &mut Cs, g: &Group, bits_be: &Vec<Boolean>) -> Group {
    g_mul_from(cs, g, bits_be, 0, g_zero())
}

fn g_mul_from(cs: &mut Cs, base: &Group, bits: &Vec<Boolean>, i: usize, output: Group) -> Group {
    if i < bits.len() {
        let next = g_mul_step(cs, &bits[i], base, &output);
        g_mul_from(cs, base, bits, i + 1, next)
    } else {
        output
    }
}

/// mul.rs `mul_assign` by a scalar: `to_bits_be` of the scalar.
pub fn g_mul(cs: &mut Cs, g: &Group, s: &Field) -> Group {
    let le = s_to_bits_le(cs, s);
    let be = bits_rev(&le);
    g_mul_bits(cs, g, &be)
}

fn bools_to_consts(k: &Vec<bool>) -> Vec<Boolean> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < k.len() {
        out.push(b_const(k[i]));
        i += 1;
    }
    out
}

/// lib.rs `is_in_group`: `[r]self` by the 256 big-endian bits of r, then `is_zero`.
pub fn g_is_in_group(cs: &mut Cs, g: &Group) -> Boolean {
    let r_le = limbs_bits(&R, 256);
    let r_be = bools_to_consts(&bools_rev(&r_le));
    let prod = g_mul_bits(cs, g, &r_be);
    g_is_zero(cs, &prod)
}

pub struct SqrtFlagged {
    pub first: Field,
    pub second: Field,
    pub err: Boolean,
}

/// square_root.rs `square_roots_flagged_nondeterministic` on a variable.
pub fn f_square_roots_flagged(cs: &mut Cs, x: &Field) -> SqrtFlagged {
    let euler = f_pow_const(cs, x, &p_half_bits_be());
    let is_nonzero_square = f_is_one(cs, &euler);
    let square = f_ternary(cs, &is_nonzero_square, x, &f_of(lc_zero()));
    let first = f_new(cs);
    enforce(cs, lc_copy(&first.lc), lc_copy(&first.lc), lc_copy(&square.lc));
    let second = f_of(lc_neg(&first.lc));
    let is_zero = f_is_zero(cs, x);
    let is_nonzero = b_not(&is_zero);
    let err = b_and(cs, &is_nonzero, &b_not(&is_nonzero_square));
    SqrtFlagged { first, second, err }
}

/// helpers/from_x_coordinate.rs `from_x_coordinate_flagged`.
pub fn g_from_x_coordinate_flagged(cs: &mut Cs, x: &Field) -> (Group, Boolean) {
    let a = f_of(lc_const(EDWARDS_A, 0));
    let d = f_of(lc_const(EDWARDS_D, 0));
    let xx = f_mul(cs, x, x);
    let axx = f_mul(cs, &a, &xx);
    let a_xx_minus_1 = f_sub(&axx, &f_of(lc_one()));
    let dxx = f_mul(cs, &d, &xx);
    let d_xx_minus_1 = f_sub(&dxx, &f_of(lc_one()));
    let yy = f_new(cs);
    enforce(cs, lc_copy(&yy.lc), lc_copy(&d_xx_minus_1.lc), lc_copy(&a_xx_minus_1.lc));
    let r = f_square_roots_flagged(cs, &yy);
    let point1 = Group { x: f_copy(x), y: f_copy(&r.first) };
    let point2 = Group { x: f_copy(x), y: f_copy(&r.second) };
    let b1 = g_is_in_group(cs, &point1);
    let b2 = g_is_in_group(cs, &point2);
    let y2_or_zero = f_ternary(cs, &b2, &r.second, &f_of(lc_zero()));
    let y1_or_y2_or_zero = f_ternary(cs, &b1, &r.first, &y2_or_zero);
    let y = f_ternary(cs, &r.err, &f_of(lc_zero()), &y1_or_y2_or_zero);
    let neither = b_and(cs, &b_not(&b1), &b_not(&b2));
    let flag = b_or(cs, &r.err, &neither);
    (Group { x: f_copy(x), y }, flag)
}

/// 0 square_roots_flagged_nondeterministic, 1 from_x_coordinate_flagged, on
/// the private input W1.
pub fn h_flagged(op: u32) -> Cs {
    let mut cs = cs_new();
    let x = f_new(&mut cs);
    if op == 0 {
        let _ = f_square_roots_flagged(&mut cs, &x);
    } else {
        let _ = g_from_x_coordinate_flagged(&mut cs, &x);
    }
    cs
}

fn bools_rev(x: &Vec<bool>) -> Vec<bool> {
    let mut out = Vec::new();
    let mut i = x.len();
    while i > 0 {
        i -= 1;
        out.push(x[i]);
    }
    out
}

// ---------------------------------------------------------------------------
// circuit/types/address. An address is its group element; equality, ternary,
// bits, new, and the conversions from bits and fields are the Group ones.

/// compare.rs: the field comparison of the abscissas. `op`: 0 is_less_than,
/// 1 is_greater_than, 2 is_less_than_or_equal, 3 is_greater_than_or_equal.
pub fn a_compare(cs: &mut Cs, a: &Group, b: &Group, op: u32) -> Boolean {
    if op == 0 {
        f_is_less_than(cs, &a.x, &b.x)
    } else if op == 1 {
        f_is_less_than(cs, &b.x, &a.x)
    } else if op == 2 {
        let gt = f_is_less_than(cs, &b.x, &a.x);
        b_not(&gt)
    } else {
        let r = f_is_less_than(cs, &a.x, &b.x);
        b_not(&r)
    }
}

/// helpers/to_field.rs: the abscissa, no constraint.
pub fn a_to_field(a: &Group) -> Field {
    f_copy(&a.x)
}

/// helpers/from_group.rs: the same point, no constraint.
pub fn a_from_group(g: &Group) -> Group {
    g_copy(g)
}

// ---------------------------------------------------------------------------
// Harnesses: inputs are fresh wires 1, 2, ... in argument order.

fn in_bits(cs: &mut Cs, n: usize) -> Vec<Boolean> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < n {
        out.push(b_var(new_var(cs)));
        i += 1;
    }
    out
}

pub fn h_enforce() -> Cs {
    let mut cs = cs_new();
    let a = new_var(&mut cs);
    let b = new_var(&mut cs);
    let c = new_var(&mut cs);
    enforce(&mut cs, lc_var(a), lc_var(b), lc_var(c));
    cs
}

pub fn h_assert() -> Cs {
    let mut cs = cs_new();
    let b = new_var(&mut cs);
    env_assert(&mut cs, &lc_var(b));
    cs
}

pub fn h_assert_eq() -> Cs {
    let mut cs = cs_new();
    let a = new_var(&mut cs);
    let b = new_var(&mut cs);
    env_assert_eq(&mut cs, &lc_var(a), &lc_var(b));
    cs
}

pub fn h_assert_neq() -> Cs {
    let mut cs = cs_new();
    let a = new_var(&mut cs);
    let b = new_var(&mut cs);
    env_assert_neq(&mut cs, &lc_var(a), &lc_var(b));
    cs
}

pub fn h_b_new() -> Cs {
    let mut cs = cs_new();
    let _ = b_new(&mut cs);
    cs
}

/// Boolean binary operations: 0 AND, 1 OR, 2 XOR, 3 NAND, 4 NOR,
/// 5 is_equal, 6 is_not_equal.
pub fn h_b_binop(op: u32) -> Cs {
    let mut cs = cs_new();
    let x = b_var(new_var(&mut cs));
    let y = b_var(new_var(&mut cs));
    let _ = if op == 0 {
        b_and(&mut cs, &x, &y)
    } else if op == 1 {
        b_or(&mut cs, &x, &y)
    } else if op == 2 {
        b_xor(&mut cs, &x, &y)
    } else if op == 3 {
        b_nand(&mut cs, &x, &y)
    } else if op == 4 {
        b_nor(&mut cs, &x, &y)
    } else if op == 5 {
        b_is_equal(&mut cs, &x, &y)
    } else {
        b_is_not_equal(&mut cs, &x, &y)
    };
    cs
}

pub fn h_b_ternary() -> Cs {
    let mut cs = cs_new();
    let c = b_var(new_var(&mut cs));
    let x = b_var(new_var(&mut cs));
    let y = b_var(new_var(&mut cs));
    let _ = b_ternary(&mut cs, &c, &x, &y);
    cs
}

/// `sub` selects the subtractor.
pub fn h_b_adder(sub: bool) -> Cs {
    let mut cs = cs_new();
    let x = b_var(new_var(&mut cs));
    let y = b_var(new_var(&mut cs));
    let c = b_var(new_var(&mut cs));
    let _ = if sub { b_subtractor(&mut cs, &x, &y, &c) } else { b_adder(&mut cs, &x, &y, &c) };
    cs
}

pub fn h_b_assert_bits_are_zero(n: usize) -> Cs {
    let mut cs = cs_new();
    let bits = in_bits(&mut cs, n);
    b_assert_bits_are_zero(&mut cs, &bits);
    cs
}

/// The constant is given by its little-endian bits; `assert` selects the asserting form.
pub fn h_b_lte_const(consts: &Vec<bool>, assert: bool) -> Cs {
    let mut cs = cs_new();
    let bits = in_bits(&mut cs, consts.len());
    if assert {
        b_assert_less_than_or_equal_constant(&mut cs, &bits, consts);
    } else {
        let _ = b_is_less_than_or_equal_constant(&mut cs, &bits, consts);
    }
    cs
}

/// Field binary operations: 0 mul, 1 div, 2 is_equal, 3 is_not_equal,
/// 4 is_less_than, 5 is_greater_than, 6 is_less_than_or_equal,
/// 7 is_greater_than_or_equal, 8 pow.
pub fn h_f_binop(op: u32) -> Cs {
    let mut cs = cs_new();
    let x = f_new(&mut cs);
    let y = f_new(&mut cs);
    if op == 0 {
        let _ = f_mul(&mut cs, &x, &y);
    } else if op == 1 {
        let _ = f_div(&mut cs, &x, &y);
    } else if op == 2 {
        let _ = f_is_equal(&mut cs, &x, &y);
    } else if op == 3 {
        let _ = f_is_not_equal(&mut cs, &x, &y);
    } else if op == 4 {
        let _ = f_is_less_than(&mut cs, &x, &y);
    } else if op == 5 {
        let _ = f_is_greater_than(&mut cs, &x, &y);
    } else if op == 6 {
        let _ = f_is_less_than_or_equal(&mut cs, &x, &y);
    } else if op == 7 {
        let _ = f_is_greater_than_or_equal(&mut cs, &x, &y);
    } else {
        let _ = f_pow(&mut cs, &x, &y);
    }
    cs
}

/// Field unary operations: 0 square, 1 inverse, 2 is_zero, 3 is_one,
/// 4 write_bits_le, 5 write_bits_be, 6 square_root, 7 even_square_root.
pub fn h_f_unop(op: u32) -> Cs {
    let mut cs = cs_new();
    let x = f_new(&mut cs);
    if op == 0 {
        let _ = f_square(&mut cs, &x);
    } else if op == 1 {
        let _ = f_inverse(&mut cs, &x);
    } else if op == 2 {
        let _ = f_is_zero(&mut cs, &x);
    } else if op == 3 {
        let _ = f_is_one(&mut cs, &x);
    } else if op == 4 {
        let _ = f_to_bits_le(&mut cs, &x);
    } else if op == 5 {
        let _ = f_to_bits_be(&mut cs, &x);
    } else if op == 6 {
        let _ = f_square_root(&mut cs, &x);
    } else {
        let _ = f_even_square_root(&mut cs, &x);
    }
    cs
}

pub fn h_f_ternary() -> Cs {
    let mut cs = cs_new();
    let c = b_var(new_var(&mut cs));
    let x = f_new(&mut cs);
    let y = f_new(&mut cs);
    let _ = f_ternary(&mut cs, &c, &x, &y);
    cs
}

/// `Field::from_bits_le` (or `_be`) of `n` input bits.
pub fn h_f_from_bits(n: usize, be: bool) -> Cs {
    let mut cs = cs_new();
    let bits = in_bits(&mut cs, n);
    let _ = if be { f_from_bits_be(&mut cs, &bits) } else { f_from_bits_le(&mut cs, &bits) };
    cs
}

/// lib.rs `From<&LinearCombination>`: no constraint.
pub fn h_f_from() -> Cs {
    let mut cs = cs_new();
    let v = new_var(&mut cs);
    let _ = f_of(lc_copy(&lc_var(v)));
    cs
}

/// `Field::from_boolean` and `From<Boolean>`: no constraint.
pub fn h_f_from_boolean() -> Cs {
    let mut cs = cs_new();
    let b = b_var(new_var(&mut cs));
    let _ = f_from_boolean(&b);
    cs
}

fn in_int(cs: &mut Cs, n: usize, signed: bool) -> Integer {
    Integer { bits: in_bits(cs, n), signed }
}

/// Integer binary operations on two `n`-bit inputs: 0 AND, 1 OR, 2 XOR,
/// 3 is_equal, 4 is_not_equal, 5 add_checked, 6 add_wrapped, 7 sub_checked,
/// 8 sub_wrapped, 9..12 the comparisons (`i_compare`), 13 mul_wrapped,
/// 14 mul_checked, 15 karatsuba_multiply, 16 div_wrapped, 17 div_checked,
/// 18 rem_wrapped, 19 rem_checked.
pub fn h_i_binop(n: usize, signed: bool, op: u32) -> Cs {
    let mut cs = cs_new();
    let x = in_int(&mut cs, n, signed);
    let y = in_int(&mut cs, n, signed);
    if op <= 2 {
        let _ = i_bitwise(&mut cs, &x, &y, op);
    } else if op == 3 {
        let _ = i_is_equal(&mut cs, &x, &y);
    } else if op == 4 {
        let _ = i_is_not_equal(&mut cs, &x, &y);
    } else if op == 5 {
        let _ = i_add_checked(&mut cs, &x, &y);
    } else if op == 6 {
        let _ = i_add_wrapped(&mut cs, &x, &y);
    } else if op == 7 {
        let _ = i_sub_checked(&mut cs, &x, &y);
    } else if op == 8 {
        let _ = i_sub_wrapped(&mut cs, &x, &y);
    } else if op <= 12 {
        let _ = i_compare(&mut cs, &x, &y, op - 9);
    } else if op == 13 {
        let _ = i_mul_wrapped(&mut cs, &x, &y);
    } else if op == 14 {
        let _ = i_mul_checked(&mut cs, &x, &y);
    } else if op == 15 {
        let _ = i_karatsuba_multiply(&mut cs, &x, &y);
    } else if op == 16 {
        let _ = i_div_rem(&mut cs, &x, &y, false, false);
    } else if op == 17 {
        let _ = i_div_rem(&mut cs, &x, &y, true, false);
    } else if op == 18 {
        let _ = i_div_rem(&mut cs, &x, &y, false, true);
    } else {
        let _ = i_div_rem(&mut cs, &x, &y, true, true);
    }
    cs
}

/// Integer unary operations on an `n`-bit input: 0 new, 1 is_zero, 2 is_one,
/// 3 abs_checked, 4 abs_wrapped, 5 neg, 6 to_field (and to_fields),
/// 7 write_bits_le and write_bits_be, 8 to_scalar.
pub fn h_i_unop(n: usize, signed: bool, op: u32) -> Cs {
    let mut cs = cs_new();
    if op == 0 {
        let _ = i_new(&mut cs, n, signed);
    } else {
        let x = in_int(&mut cs, n, signed);
        if op == 1 {
            let _ = i_is_zero(&mut cs, &x);
        } else if op == 2 {
            let _ = i_is_one(&mut cs, &x);
        } else if op == 3 {
            let _ = i_abs(&mut cs, &x, true);
        } else if op == 4 {
            let _ = i_abs(&mut cs, &x, false);
        } else if op == 5 {
            let _ = i_neg(&mut cs, &x);
        } else if op == 6 {
            let _ = i_to_field(&mut cs, &x);
        } else if op == 8 {
            let _ = i_to_scalar(&mut cs, &x);
        } else {
            let _ = bits_copy(&x.bits);
        }
    }
    cs
}

/// Shifts of an `n`-bit input by an `m`-bit unsigned amount: 0 shl_wrapped,
/// 1 shl_checked, 2 shr_wrapped, 3 shr_checked.
pub fn h_i_shift(n: usize, signed: bool, m: usize, op: u32) -> Cs {
    let mut cs = cs_new();
    let x = in_int(&mut cs, n, signed);
    let e = in_int(&mut cs, m, false);
    if op == 0 {
        let _ = i_shl_wrapped(&mut cs, &x, &e);
    } else if op == 1 {
        let _ = i_shl_checked(&mut cs, &x, &e);
    } else if op == 2 {
        let _ = i_shr_wrapped(&mut cs, &x, &e);
    } else {
        let _ = i_shr_checked(&mut cs, &x, &e);
    }
    cs
}

pub fn h_i_ternary(n: usize, signed: bool) -> Cs {
    let mut cs = cs_new();
    let c = b_var(new_var(&mut cs));
    let x = in_int(&mut cs, n, signed);
    let y = in_int(&mut cs, n, signed);
    let _ = i_ternary(&mut cs, &c, &x, &y);
    cs
}

/// `Integer::from_bits_le` (or `_be`) of `m` input bits to an `n`-bit integer.
pub fn h_i_from_bits(m: usize, n: usize, signed: bool, be: bool) -> Cs {
    let mut cs = cs_new();
    let bits = in_bits(&mut cs, m);
    let _ = if be { i_from_bits_be(&mut cs, &bits, n, signed) } else { i_from_bits_le(&mut cs, &bits, n, signed) };
    cs
}

/// `Integer::from_field` (`lossy` selects `from_field_lossy`) of a field input.
pub fn h_i_from_field(n: usize, signed: bool, lossy: bool) -> Cs {
    let mut cs = cs_new();
    let f = f_new(&mut cs);
    let _ = if lossy { i_from_field_lossy(&mut cs, &f, n, signed) } else { i_from_field(&mut cs, &f, n, signed) };
    cs
}

/// Scalar binary operations: 0 is_equal, 1 is_not_equal, 2..5 the
/// comparisons (`s_compare`), 6 add.
pub fn h_s_binop(op: u32) -> Cs {
    let mut cs = cs_new();
    let x = s_new(&mut cs);
    let y = s_new(&mut cs);
    if op == 0 {
        let _ = f_is_equal(&mut cs, &x, &y);
    } else if op == 1 {
        let r = f_is_equal(&mut cs, &x, &y);
        let _ = b_not(&r);
    } else if op <= 5 {
        let _ = s_compare(&mut cs, &x, &y, op - 2);
    } else {
        let _ = s_add(&mut cs, &x, &y);
    }
    cs
}

/// Scalar unary operations: 0 is_zero, 1 is_one, 2 write_bits_le (and _be),
/// 3 from_field, 4 from_field_lossy (the input of 3 and 4 is a field).
pub fn h_s_unop(op: u32) -> Cs {
    let mut cs = cs_new();
    let x = s_new(&mut cs);
    if op == 0 {
        let _ = f_is_zero(&mut cs, &x);
    } else if op == 1 {
        let _ = f_is_one(&mut cs, &x);
    } else if op == 2 {
        let _ = s_to_bits_le(&mut cs, &x);
    } else {
        let bits = f_to_bits_le(&mut cs, &x);
        if op == 3 {
            let _ = s_from_bits_le(&mut cs, &bits);
        } else {
            let _ = s_from_bits_le(&mut cs, &bits_range(&bits, 0, SCALAR_DATA_BITS));
        }
    }
    cs
}

pub fn h_s_ternary() -> Cs {
    let mut cs = cs_new();
    let c = b_var(new_var(&mut cs));
    let x = s_new(&mut cs);
    let y = s_new(&mut cs);
    let _ = f_ternary(&mut cs, &c, &x, &y);
    cs
}

/// `Scalar::from_bits_le` of `n` input bits.
pub fn h_s_from_bits(n: usize) -> Cs {
    let mut cs = cs_new();
    let bits = in_bits(&mut cs, n);
    let _ = s_from_bits_le(&mut cs, &bits);
    cs
}

fn in_group(cs: &mut Cs) -> Group {
    let x = f_new(cs);
    let y = f_new(cs);
    Group { x, y }
}

/// Group binary operations on (W1, W2) and (W3, W4): 0 add, 1 sub,
/// 2 is_equal, 3 is_not_equal, 4 enforce_double (the second is the double).
pub fn h_g_binop(op: u32) -> Cs {
    let mut cs = cs_new();
    let a = in_group(&mut cs);
    let b = in_group(&mut cs);
    if op == 0 {
        let _ = g_add(&mut cs, &a, &b);
    } else if op == 1 {
        let _ = g_sub(&mut cs, &a, &b);
    } else if op == 2 {
        let _ = g_is_equal(&mut cs, &a, &b);
    } else if op == 3 {
        let _ = g_is_not_equal(&mut cs, &a, &b);
    } else {
        g_enforce_double(&mut cs, &a, &b);
    }
    cs
}

/// Group unary operations on (W1, W2): 0 double, 1 mul_by_cofactor,
/// 2 enforce_on_curve, 3 enforce_in_group (and new, from_xy_coordinates),
/// 4 is_zero, 5 write_bits_le (and _be), 6 is_in_group, 7 from_x_coordinate
/// of W1.
pub fn h_g_unop(op: u32) -> Cs {
    let mut cs = cs_new();
    let a = in_group(&mut cs);
    if op == 0 {
        let _ = g_double(&mut cs, &a);
    } else if op == 1 {
        let _ = g_mul_by_cofactor(&mut cs, &a);
    } else if op == 2 {
        g_enforce_on_curve(&mut cs, &a);
    } else if op == 3 {
        let _ = g_from_xy_coordinates(&mut cs, &a.x, &a.y);
    } else if op == 4 {
        let _ = g_is_zero(&mut cs, &a);
    } else if op == 5 {
        let _ = g_to_bits_le(&mut cs, &a);
    } else if op == 6 {
        let _ = g_is_in_group(&mut cs, &a);
    } else {
        let _ = g_from_x_coordinate(&mut cs, &a.x);
    }
    cs
}

/// Condition W1, first (W2, W3), second (W4, W5).
pub fn h_g_ternary() -> Cs {
    let mut cs = cs_new();
    let c = b_var(new_var(&mut cs));
    let a = in_group(&mut cs);
    let b = in_group(&mut cs);
    let _ = g_ternary(&mut cs, &c, &a, &b);
    cs
}

/// Group (W1, W2) times scalar W3.
pub fn h_g_mul() -> Cs {
    let mut cs = cs_new();
    let a = in_group(&mut cs);
    let s = s_new(&mut cs);
    let _ = g_mul(&mut cs, &a, &s);
    cs
}

/// `Group::from_bits_le` (or `_be`) of `n` input bits.
pub fn h_g_from_bits(n: usize, be: bool) -> Cs {
    let mut cs = cs_new();
    let bits = in_bits(&mut cs, n);
    if be {
        let _ = g_from_bits_be(&mut cs, &bits);
    } else {
        let _ = g_from_bits_le(&mut cs, &bits);
    }
    cs
}

/// Address comparisons of (W1, W2) and (W3, W4), `op` as in `a_compare`.
pub fn h_a_compare(op: u32) -> Cs {
    let mut cs = cs_new();
    let a = in_group(&mut cs);
    let b = in_group(&mut cs);
    let _ = a_compare(&mut cs, &a, &b, op);
    cs
}

/// 0 `Field::from(Address)`, 1 `Address::from(Group)`.
pub fn h_a_convert(op: u32) -> Cs {
    let mut cs = cs_new();
    let a = in_group(&mut cs);
    if op == 0 {
        let _ = a_to_field(&a);
    } else {
        let _ = a_from_group(&a);
    }
    cs
}

/// Integer pow of an `n`-bit base (W1..) by an unsigned `m`-bit exponent:
/// 0 pow_wrapped, 1 pow_checked (and pow).
pub fn h_i_pow(n: usize, signed: bool, m: usize, op: u32) -> Cs {
    let mut cs = cs_new();
    let x = in_int(&mut cs, n, signed);
    let e = in_int(&mut cs, m, false);
    if op == 0 {
        let _ = i_pow_wrapped(&mut cs, &x, &e);
    } else {
        let _ = i_pow_checked(&mut cs, &x, &e);
    }
    cs
}

/// Unsigned modulo of two `n`-bit integers.
pub fn h_i_modulo(n: usize) -> Cs {
    let mut cs = cs_new();
    let x = in_int(&mut cs, n, false);
    let y = in_int(&mut cs, n, false);
    let _ = i_modulo(&mut cs, &x, &y);
    cs
}

// ---------------------------------------------------------------------------
// circuit/account and circuit/collections.

pub struct Fields2 {
    pub a: Field,
    pub b: Field,
}

/// compute_key/helpers/to_fields.rs: the abscissas of pk_sig and pr_sig.
pub fn ck_to_fields(pk_sig: &Group, pr_sig: &Group) -> Fields2 {
    Fields2 { a: f_copy(&pk_sig.x), b: f_copy(&pr_sig.x) }
}

/// signature/helpers/to_fields.rs: challenge and response (`Scalar::to_field`
/// is the scalar's field) and the compute key's fields.
pub fn sig_to_fields(challenge: &Field, response: &Field, pk_sig: &Group, pr_sig: &Group) -> Vec<Field> {
    let ck = ck_to_fields(pk_sig, pr_sig);
    let mut out = Vec::new();
    out.push(f_copy(challenge));
    out.push(f_copy(response));
    out.push(ck.a);
    out.push(ck.b);
    out
}

/// kary_merkle_tree/helpers/mod.rs `BooleanHash::new`: `Boolean::new` per bit.
pub fn bh_new(cs: &mut Cs, variant: usize) -> Vec<Boolean> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < variant {
        out.push(b_new(cs));
        i += 1;
    }
    out
}

/// 0 ComputeKey::to_fields of (W1, W2), (W3, W4); 1 Signature::to_fields of
/// scalars W1, W2 and the compute key (W3, W4), (W5, W6).
pub fn h_account_to_fields(op: u32) -> Cs {
    let mut cs = cs_new();
    if op == 0 {
        let pk = in_group(&mut cs);
        let pr = in_group(&mut cs);
        let _ = ck_to_fields(&pk, &pr);
    } else {
        let c = s_new(&mut cs);
        let r = s_new(&mut cs);
        let pk = in_group(&mut cs);
        let pr = in_group(&mut cs);
        let _ = sig_to_fields(&c, &r, &pk, &pr);
    }
    cs
}

pub struct ComputeKey {
    pub pk_sig: Group,
    pub pr_sig: Group,
    pub sk_prf: Field,
}

pub struct Signature {
    pub challenge: Field,
    pub response: Field,
    pub compute_key: ComputeKey,
}

fn in_compute_key(cs: &mut Cs) -> ComputeKey {
    let pk_sig = in_group(cs);
    let pr_sig = in_group(cs);
    let sk_prf = s_new(cs);
    ComputeKey { pk_sig, pr_sig, sk_prf }
}

fn in_signature(cs: &mut Cs) -> Signature {
    let challenge = s_new(cs);
    let response = s_new(cs);
    let compute_key = in_compute_key(cs);
    Signature { challenge, response, compute_key }
}

/// compute_key/equal.rs: `(pk_sig == pk_sig') & (pr_sig == pr_sig')` is
/// evaluated before `sk_prf == sk_prf'`.
pub fn ck_is_equal(cs: &mut Cs, a: &ComputeKey, b: &ComputeKey) -> Boolean {
    let pk = g_is_equal(cs, &a.pk_sig, &b.pk_sig);
    let pr = g_is_equal(cs, &a.pr_sig, &b.pr_sig);
    let t = b_and(cs, &pk, &pr);
    let sk = f_is_equal(cs, &a.sk_prf, &b.sk_prf);
    b_and(cs, &t, &sk)
}

/// signature/equal.rs.
pub fn sig_is_equal(cs: &mut Cs, a: &Signature, b: &Signature) -> Boolean {
    let c = f_is_equal(cs, &a.challenge, &b.challenge);
    let r = f_is_equal(cs, &a.response, &b.response);
    let t = b_and(cs, &c, &r);
    let ck = ck_is_equal(cs, &a.compute_key, &b.compute_key);
    b_and(cs, &t, &ck)
}

/// compute_key/ternary.rs.
pub fn ck_ternary(cs: &mut Cs, c: &Boolean, a: &ComputeKey, b: &ComputeKey) -> ComputeKey {
    let pk_sig = g_ternary(cs, c, &a.pk_sig, &b.pk_sig);
    let pr_sig = g_ternary(cs, c, &a.pr_sig, &b.pr_sig);
    let sk_prf = f_ternary(cs, c, &a.sk_prf, &b.sk_prf);
    ComputeKey { pk_sig, pr_sig, sk_prf }
}

/// signature/ternary.rs.
pub fn sig_ternary(cs: &mut Cs, c: &Boolean, a: &Signature, b: &Signature) -> Signature {
    let challenge = f_ternary(cs, c, &a.challenge, &b.challenge);
    let response = f_ternary(cs, c, &a.response, &b.response);
    let compute_key = ck_ternary(cs, c, &a.compute_key, &b.compute_key);
    Signature { challenge, response, compute_key }
}

/// signature/helpers/to_bits.rs `write_bits_le`; `write_bits_be` reverses each
/// component's bits and adds the same constraints.
pub fn sig_write_bits_le(cs: &mut Cs, s: &Signature) -> Vec<Boolean> {
    let c = s_to_bits_le(cs, &s.challenge);
    let r = s_to_bits_le(cs, &s.response);
    let pk = g_to_bits_le(cs, &s.compute_key.pk_sig);
    let pr = g_to_bits_le(cs, &s.compute_key.pr_sig);
    bits_append(&bits_append(&c, &r), &bits_append(&pk, &pr))
}

/// 0 ComputeKey is_equal, 1 is_not_equal of (W1..W5) and (W6..W10);
/// 2 Signature is_equal, 3 is_not_equal of (W1..W7) and (W8..W14).
pub fn h_account_equal(op: u32) -> Cs {
    let mut cs = cs_new();
    if op < 2 {
        let a = in_compute_key(&mut cs);
        let b = in_compute_key(&mut cs);
        let r = ck_is_equal(&mut cs, &a, &b);
        if op == 1 {
            let _ = b_not(&r);
        }
    } else {
        let a = in_signature(&mut cs);
        let b = in_signature(&mut cs);
        let r = sig_is_equal(&mut cs, &a, &b);
        if op == 3 {
            let _ = b_not(&r);
        }
    }
    cs
}

/// Condition W1, signatures (W2..W8) and (W9..W15).
pub fn h_sig_ternary() -> Cs {
    let mut cs = cs_new();
    let c = b_var(new_var(&mut cs));
    let a = in_signature(&mut cs);
    let b = in_signature(&mut cs);
    let _ = sig_ternary(&mut cs, &c, &a, &b);
    cs
}

/// Signature (W1..W7) `write_bits_le`.
pub fn h_sig_write_bits() -> Cs {
    let mut cs = cs_new();
    let s = in_signature(&mut cs);
    let _ = sig_write_bits_le(&mut cs, &s);
    cs
}

/// kary_merkle_tree/helpers/mod.rs `BooleanHash::is_equal`: the lazy map
/// interleaves each bit comparison with the AND fold from constant true.
pub fn bh_is_equal(cs: &mut Cs, a: &Vec<Boolean>, b: &Vec<Boolean>) -> Boolean {
    let mut acc = b_const(true);
    let mut i = 0;
    while i < a.len() {
        let e = b_is_equal(cs, &a[i], &b[i]);
        acc = b_and(cs, &acc, &e);
        i += 1;
    }
    acc
}

pub fn bh_ternary(cs: &mut Cs, c: &Boolean, a: &Vec<Boolean>, b: &Vec<Boolean>) -> Vec<Boolean> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < a.len() {
        out.push(b_ternary(cs, c, &a[i], &b[i]));
        i += 1;
    }
    out
}

/// BooleanHash of `n` bits: 0 is_equal, 1 is_not_equal of W1..Wn and
/// Wn+1..W2n; 2 ternary with condition W1 of W2..Wn+1 and Wn+2..W2n+1.
pub fn h_bh_op(n: usize, op: u32) -> Cs {
    let mut cs = cs_new();
    if op < 2 {
        let a = in_bits(&mut cs, n);
        let b = in_bits(&mut cs, n);
        let r = bh_is_equal(&mut cs, &a, &b);
        if op == 1 {
            let _ = b_not(&r);
        }
    } else {
        let c = b_var(new_var(&mut cs));
        let a = in_bits(&mut cs, n);
        let b = in_bits(&mut cs, n);
        let _ = bh_ternary(&mut cs, &c, &a, &b);
    }
    cs
}

/// data/ciphertext/equal.rs `is_equal`: `equal &= a.is_equal(b)` from
/// constant true; vectors of different lengths are constant false.
pub fn ct_is_equal(cs: &mut Cs, a: &Vec<Field>, b: &Vec<Field>) -> Boolean {
    if a.len() != b.len() {
        b_const(false)
    } else {
        let mut acc = b_const(true);
        let mut i = 0;
        while i < a.len() {
            let e = f_is_equal(cs, &a[i], &b[i]);
            acc = b_and(cs, &acc, &e);
            i += 1;
        }
        acc
    }
}

/// `is_not_equal`: `not_equal |= a.is_not_equal(b)` from constant false.
pub fn ct_is_not_equal(cs: &mut Cs, a: &Vec<Field>, b: &Vec<Field>) -> Boolean {
    if a.len() != b.len() {
        b_const(true)
    } else {
        let mut acc = b_const(false);
        let mut i = 0;
        while i < a.len() {
            let e = f_is_not_equal(cs, &a[i], &b[i]);
            acc = b_or(cs, &acc, &e);
            i += 1;
        }
        acc
    }
}

/// data/ciphertext/to_bits.rs: `Field::write_bits_le` per element.
pub fn ct_write_bits_le(cs: &mut Cs, a: &Vec<Field>) -> Vec<Boolean> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < a.len() {
        let bits = f_to_bits_le(cs, &a[i]);
        out = bits_append(&out, &bits);
        i += 1;
    }
    out
}

fn in_fields(cs: &mut Cs, n: usize) -> Vec<Field> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < n {
        out.push(f_new(cs));
        i += 1;
    }
    out
}

/// Ciphertexts of `n` and `m` fields W1..Wn, Wn+1..Wn+m: 0 is_equal,
/// 1 is_not_equal; 2 `Ciphertext::new` of `n` fields; 3 write_bits_le of W1..Wn
/// (write_bits_be adds the same constraints).
pub fn h_ct_op(n: usize, m: usize, op: u32) -> Cs {
    let mut cs = cs_new();
    let a = in_fields(&mut cs, n);
    if op == 0 {
        let b = in_fields(&mut cs, m);
        let _ = ct_is_equal(&mut cs, &a, &b);
    } else if op == 1 {
        let b = in_fields(&mut cs, m);
        let _ = ct_is_not_equal(&mut cs, &a, &b);
    } else if op == 3 {
        let _ = ct_write_bits_le(&mut cs, &a);
    }
    cs
}

/// state_path/helpers `HeaderLeaf` (0: u8 index), `TransactionLeaf` (1: u8
/// variant, u16 index) and `TransitionLeaf` (2: u8 version, index and variant)
/// `write_bits_le`: the integers' bits are copied, then `Field::write_bits_le`
/// of the id. `write_bits_be` adds the same constraints.
pub fn h_leaf_write_bits(kind: u32) -> Cs {
    let mut cs = cs_new();
    let mut bits = Vec::new();
    if kind == 0 {
        let index = in_int(&mut cs, 8, false);
        bits = bits_append(&bits, &index.bits);
    } else if kind == 1 {
        let variant = in_int(&mut cs, 8, false);
        let index = in_int(&mut cs, 16, false);
        bits = bits_append(&bits_append(&bits, &variant.bits), &index.bits);
    } else {
        let version = in_int(&mut cs, 8, false);
        let index = in_int(&mut cs, 8, false);
        let variant = in_int(&mut cs, 8, false);
        bits = bits_append(&bits_append(&bits_append(&bits, &version.bits), &index.bits), &variant.bits);
    }
    let id = f_new(&mut cs);
    let id_bits = f_to_bits_le(&mut cs, &id);
    let _ = bits_append(&bits, &id_bits);
    cs
}

/// data/identifier/to_bits.rs: `Field::write_bits_le` truncated to `8 * size`.
pub fn id_write_bits_le(cs: &mut Cs, x: &Field, size: usize) -> Vec<Boolean> {
    let bits = f_to_bits_le(cs, x);
    bits_range(&bits, 0, 8 * size)
}

/// 0 Identifier W1 of `n` bytes; 1 ProgramID with name W1 of `n` bytes and
/// network W2 of `m` bytes (id/to_bits.rs: name, then network).
pub fn h_id_write_bits(op: u32, n: usize, m: usize) -> Cs {
    let mut cs = cs_new();
    let name = f_new(&mut cs);
    if op == 0 {
        let _ = id_write_bits_le(&mut cs, &name, n);
    } else {
        let network = f_new(&mut cs);
        let a = id_write_bits_le(&mut cs, &name, n);
        let b = id_write_bits_le(&mut cs, &network, m);
        let _ = bits_append(&a, &b);
    }
    cs
}

/// data/record/helpers/owner.rs on owners (W1, W2) and (W3, W4), `pa` and `pb`
/// their visibilities: 0 is_equal, 1 is_not_equal (`Address::is_equal` when
/// the variants agree, else a constant); 2 `Owner::new` of (W1, W2), which is
/// `Address::new`; 3 `to_entry` (no constraint).
pub fn h_owner(op: u32, pa: bool, pb: bool) -> Cs {
    let mut cs = cs_new();
    let a = in_group(&mut cs);
    if op < 2 {
        let b = in_group(&mut cs);
        let r = if pa == pb { g_is_equal(&mut cs, &a, &b) } else { b_const(false) };
        if op == 1 {
            let _ = b_not(&r);
        }
    } else if op == 2 {
        let _ = g_from_xy_coordinates(&mut cs, &a.x, &a.y);
    }
    cs
}

/// `to_fields` of DynamicFuture and DynamicRecord: the bits with a constant
/// true appended, packed into 252-bit `Field::from_bits_le` chunks.
pub fn pack_fields(cs: &mut Cs, bits: &Vec<Boolean>) -> Vec<Field> {
    let mut all = bits_append(bits, &Vec::new());
    all.push(b_const(true));
    let mut out = Vec::new();
    let mut lo = 0;
    while lo < all.len() {
        let hi = if lo + 252 < all.len() { lo + 252 } else { all.len() };
        out.push(f_from_bits_le(cs, &bits_range(&all, lo, hi)));
        lo = hi;
    }
    out
}

/// DynamicFuture of W1..W4: 0 `new` (Field::new each), 1 write_bits_le
/// (write_bits_be adds the same constraints), 2 to_fields.
pub fn h_dynamic_future(op: u32) -> Cs {
    let mut cs = cs_new();
    let f = in_fields(&mut cs, 4);
    if op > 0 {
        let bits = ct_write_bits_le(&mut cs, &f);
        if op == 2 {
            let _ = pack_fields(&mut cs, &bits);
        }
    }
    cs
}

pub struct DynamicRecord {
    pub owner: Group,
    pub root: Field,
    pub nonce: Group,
    pub version: Integer,
}

/// data/dynamic/record/mod.rs `new`: Address::new, Field::new, Group::new and
/// U8::new in private mode.
pub fn dr_new(cs: &mut Cs) -> DynamicRecord {
    let o = in_group(cs);
    let owner = g_from_xy_coordinates(cs, &o.x, &o.y);
    let root = f_new(cs);
    let n = in_group(cs);
    let nonce = g_from_xy_coordinates(cs, &n.x, &n.y);
    let version = i_new(cs, 8, false);
    DynamicRecord { owner, root, nonce, version }
}

fn in_dynamic_record(cs: &mut Cs) -> DynamicRecord {
    let owner = in_group(cs);
    let root = f_new(cs);
    let nonce = in_group(cs);
    let version = in_int(cs, 8, false);
    DynamicRecord { owner, root, nonce, version }
}

/// to_bits.rs: owner, root and nonce field bits, then the version's bits.
pub fn dr_write_bits_le(cs: &mut Cs, r: &DynamicRecord) -> Vec<Boolean> {
    let o = g_to_bits_le(cs, &r.owner);
    let root = f_to_bits_le(cs, &r.root);
    let n = g_to_bits_le(cs, &r.nonce);
    bits_append(&bits_append(&o, &root), &bits_append(&n, &r.version.bits))
}

/// equal.rs.
pub fn dr_is_equal(cs: &mut Cs, a: &DynamicRecord, b: &DynamicRecord) -> Boolean {
    let o = g_is_equal(cs, &a.owner, &b.owner);
    let r = f_is_equal(cs, &a.root, &b.root);
    let z1 = b_and(cs, &o, &r);
    let n = g_is_equal(cs, &a.nonce, &b.nonce);
    let z2 = b_and(cs, &z1, &n);
    let v = i_is_equal(cs, &a.version, &b.version);
    b_and(cs, &z2, &v)
}

/// 0 `new`; 1 write_bits_le of (W1, W2), W3, (W4, W5), version W6..W13
/// (write_bits_be adds the same constraints); 2 to_fields; 3 is_equal and
/// 4 is_not_equal against W14..W26; 5 `find` (no constraint).
pub fn h_dynamic_record(op: u32) -> Cs {
    let mut cs = cs_new();
    if op == 0 {
        let _ = dr_new(&mut cs);
    } else {
        let a = in_dynamic_record(&mut cs);
        if op == 1 || op == 2 {
            let bits = dr_write_bits_le(&mut cs, &a);
            if op == 2 {
                let _ = pack_fields(&mut cs, &bits);
            }
        } else if op == 3 || op == 4 {
            let b = in_dynamic_record(&mut cs);
            let r = dr_is_equal(&mut cs, &a, &b);
            if op == 4 {
                let _ = b_not(&r);
            }
        }
    }
    cs
}

/// data/literal/to_fields.rs on an unconstrained literal of type code
/// `variant` as in `h_p_cast` (0 address, 1 boolean, 2 field, 3 group,
/// 4 integer of `n` bits, 5 scalar, 6 identifier literal) or 7 signature.
pub fn h_lit_to_fields(variant: u32, n: usize) -> Cs {
    let mut cs = cs_new();
    if variant == 0 || variant == 3 {
        let g = in_group(&mut cs);
        let _ = a_to_field(&g);
    } else if variant == 1 {
        let b = b_var(new_var(&mut cs));
        let _ = f_from_boolean(&b);
    } else if variant == 2 || variant == 5 {
        let f = f_new(&mut cs);
        let _ = f_copy(&f);
    } else if variant == 4 {
        let i = in_int(&mut cs, n, false);
        let _ = i_to_field(&mut cs, &i);
    } else if variant == 6 {
        let bits = in_bits(&mut cs, IL_BITS);
        let _ = il_to_field(&mut cs, &bits);
    } else {
        let s = in_signature(&mut cs);
        let _ = sig_to_fields(&s.challenge, &s.response, &s.compute_key.pk_sig, &s.compute_key.pr_sig);
    }
    cs
}

/// data/literal/equal.rs on literals of different variants: a constant, with
/// `is_not_equal` its negation.
pub fn h_lit_equal_mismatch(not: bool) -> Cs {
    let mut cs = cs_new();
    let _ = f_new(&mut cs);
    let _ = b_var(new_var(&mut cs));
    let r = b_const(false);
    if not {
        let _ = b_not(&r);
    }
    cs
}

/// kary_merkle_tree/mod.rs `KaryMerklePath::new`: `U64::new` on the leaf
/// index, then `Inject::new` on each of the `arity - 1` siblings per level,
/// a field (`variant` 0) or a BooleanHash of `variant` bits.
pub fn h_kary_path_new(depth: usize, arity: usize, variant: usize) -> Cs {
    let mut cs = cs_new();
    let _ = i_new(&mut cs, 64, false);
    let mut d = 0;
    while d < depth {
        let mut k = 0;
        while k + 1 < arity {
            if variant == 0 {
                let _ = f_new(&mut cs);
            } else {
                let _ = bh_new(&mut cs, variant);
            }
            k += 1;
        }
        d += 1;
    }
    cs
}

// ---------------------------------------------------------------------------
// circuit/algorithms/src/elligator2. The Montgomery constants are those of
// the Edwards curve: `A = 2 (a + d) / (a - d)` and `B = 4 / (a - d)`.

fn f_const(c: i128) -> Field {
    f_of(lc_const(c, 0))
}

/// encode.rs `Elligator2::encode` on a variable input.
pub fn ell2_encode(cs: &mut Cs, input: &Field) -> Group {
    env_assert_neq(cs, &input.lc, &lc_zero());
    let one = f_of(lc_one());
    let a_minus_d = f_inverse(cs, &f_const(EDWARDS_A - EDWARDS_D));
    let montgomery_a = f_mul(cs, &f_const(2 * (EDWARDS_A + EDWARDS_D)), &a_minus_d);
    let montgomery_b = f_mul(cs, &f_const(4), &a_minus_d);
    let montgomery_b_inverse = f_inverse(cs, &montgomery_b);
    let montgomery_b2 = f_square(cs, &montgomery_b);
    let montgomery_b3 = f_mul(cs, &montgomery_b2, &montgomery_b);
    let edwards_d = f_const(EDWARDS_D);
    let a = f_mul(cs, &montgomery_a, &montgomery_b_inverse);
    let half = f_inverse(cs, &f_const(2));
    let a_half = f_mul(cs, &a, &half);
    let b = f_square(cs, &montgomery_b_inverse);

    let input2 = f_square(cs, input);
    let ur2 = f_mul(cs, &edwards_d, &input2);
    let one_plus_ur2 = f_add(&one, &ur2);
    let a2 = f_square(cs, &a);
    let lhs = f_mul(cs, &a2, &ur2);
    let opu2 = f_square(cs, &one_plus_ur2);
    let rhs_neq = f_mul(cs, &b, &opu2);
    env_assert_neq(cs, &lhs.lc, &rhs_neq.lc);
    let neg_a = f_of(lc_neg(&a.lc));
    let v = f_div(cs, &neg_a, &one_plus_ur2);
    let v2 = f_square(cs, &v);
    let v3 = f_mul(cs, &v2, &v);
    let av2 = f_mul(cs, &a, &v2);
    let bv = f_mul(cs, &b, &v);
    let g = f_add(&f_add(&v3, &av2), &bv);
    let e = f_pow_const(cs, &g, &p_half_bits_be());
    let ev = f_mul(cs, &e, &v);
    let one_minus_e = f_sub(&one, &e);
    let t = f_mul(cs, &one_minus_e, &a_half);
    let x = f_sub(&ev, &t);
    let x2 = f_square(cs, &x);
    let x3 = f_mul(cs, &x2, &x);
    let ax2 = f_mul(cs, &a, &x2);
    let bx = f_mul(cs, &b, &x);
    let rhs = f_add(&f_add(&x3, &ax2), &bx);
    let root = f_new(cs);
    let root_bits = f_to_bits_be(cs, &root);
    let lsb = b_not(&root_bits[FIELD_BITS - 1]);
    env_assert(cs, &lsb.lc);
    let neg_e = f_of(lc_neg(&e.lc));
    let y = f_mul(cs, &neg_e, &root);
    let ve = f_mul(cs, &v, &e);
    let vex = f_mul(cs, &ve, &x);
    let vexy = f_mul(cs, &vex, &y);
    env_assert_neq(cs, &vexy.lc, &lc_zero());
    let y2 = f_square(cs, &y);
    env_assert_eq(cs, &y2.lc, &rhs.lc);
    let u = f_mul(cs, &x, &montgomery_b);
    let vm = f_mul(cs, &y, &montgomery_b);
    let u2 = f_mul(cs, &x2, &montgomery_b2);
    let u3 = f_mul(cs, &x3, &montgomery_b3);
    let vm2 = f_mul(cs, &y2, &montgomery_b3);
    let au2 = f_mul(cs, &montgomery_a, &u2);
    let mont = f_add(&f_add(&u3, &au2), &u);
    env_assert_eq(cs, &vm2.lc, &mont.lc);
    let ex = f_div(cs, &u, &vm);
    let u_minus_one = f_sub(&u, &one);
    let u_plus_one = f_add(&u, &one);
    let ey = f_div(cs, &u_minus_one, &u_plus_one);
    let encoding = Group { x: ex, y: ey };
    g_enforce_on_curve(cs, &encoding);
    g_mul_by_cofactor(cs, &encoding)
}

pub fn p_half_bits_be() -> Vec<bool> {
    bools_rev(&p_half_bits())
}

// ---------------------------------------------------------------------------
// circuit/algorithms/src/bhp/hasher/hash_uncompressed.rs. The base lookups
// are named constants: entry `k` of the x (`xy` 0) or y (`xy` 1) table of
// chunk `j` of window `w` is `1 + 8 (w * window_size + j) + 2 k + xy`.

pub struct MontPt {
    pub x: Field,
    pub y: Field,
}

pub struct MontC {
    pub a: Field,
    pub b: Field,
    pub half: Field,
}

fn mont_c(cs: &mut Cs) -> MontC {
    let a_minus_d = f_inverse(cs, &f_const(EDWARDS_A - EDWARDS_D));
    let a = f_mul(cs, &f_const(2 * (EDWARDS_A + EDWARDS_D)), &a_minus_d);
    let b = f_mul(cs, &f_const(4), &a_minus_d);
    let half = f_inverse(cs, &f_const(2));
    MontC { a, b, half }
}

fn bhp_lookup(cs: &mut Cs, b0: &Field, b1: &Field, b01: &Field, base: u32) -> Field {
    let t0 = f_named(cs, base);
    let t1 = f_named(cs, base + 2);
    let t2 = f_named(cs, base + 4);
    let t3 = f_named(cs, base + 6);
    let d1 = f_mul(cs, b0, &f_sub(&t1, &t0));
    let d2 = f_mul(cs, b1, &f_sub(&t2, &t0));
    let d3 = f_mul(cs, b01, &f_add(&f_sub(&f_sub(&t3, &t2), &t1), &t0));
    f_add(&f_add(&f_add(&t0, &d1), &d2), &d3)
}

/// One chunk: the Montgomery point selected by bits `i..i+3`.
fn bhp_chunk(cs: &mut Cs, bits: &Vec<Boolean>, i: usize, base: u32, mc: &MontC) -> MontPt {
    let bit_0 = f_from_boolean(&bits[i]);
    let bit_1 = f_from_boolean(&bits[i + 1]);
    let bit_2 = f_from_boolean(&bits[i + 2]);
    let b01 = b_and(cs, &bits[i], &bits[i + 1]);
    let bit_0_and_1 = f_from_boolean(&b01);
    let x = bhp_lookup(cs, &bit_0, &bit_1, &bit_0_and_1, base);
    let y = bhp_lookup(cs, &bit_0, &bit_1, &bit_0_and_1, base + 1);
    let my = f_new(cs);
    let neg_2y = lc_neg(&lc_add(&y.lc, &y.lc));
    enforce(cs, neg_2y, lc_sub(&bit_2.lc, &mc.half.lc), lc_copy(&my.lc));
    MontPt { x, y: my }
}

fn mont_add(cs: &mut Cs, this: &MontPt, that: &MontPt, mc: &MontC) -> MontPt {
    let lambda = f_new(cs);
    enforce(cs, lc_sub(&that.x.lc, &this.x.lc), lc_copy(&lambda.lc), lc_sub(&that.y.lc, &this.y.lc));
    let sum_x = f_new(cs);
    let b_lambda = f_mul(cs, &mc.b, &lambda);
    let rhs = f_add(&f_add(&f_add(&mc.a, &this.x), &that.x), &sum_x);
    enforce(cs, b_lambda.lc, lc_copy(&lambda.lc), rhs.lc);
    let sum_y = f_new(cs);
    enforce(cs, lc_sub(&this.x.lc, &sum_x.lc), lc_copy(&lambda.lc), lc_add(&this.y.lc, &sum_y.lc));
    MontPt { x: sum_x, y: sum_y }
}

/// The window of bits `lo..hi` (whole chunks) with the bases of window `w`.
fn bhp_window(cs: &mut Cs, bits: &Vec<Boolean>, lo: usize, hi: usize, w: usize, ws: usize, mc: &MontC) -> Group {
    let base0 = (1 + 8 * w * ws) as u32;
    let mut sum = bhp_chunk(cs, bits, lo, base0, mc);
    let mut j = 1;
    while lo + 3 * j < hi {
        let c = bhp_chunk(cs, bits, lo + 3 * j, base0 + 8 * (j as u32), mc);
        sum = mont_add(cs, &sum, &c, mc);
        j += 1;
    }
    let ex = f_div_unchecked(cs, &sum.x, &sum.y);
    let num = f_sub(&sum.x, &f_of(lc_one()));
    let den = f_add(&sum.x, &f_of(lc_one()));
    let ey = f_div_unchecked(cs, &num, &den);
    Group { x: ex, y: ey }
}

/// `BHPHasher::hash_uncompressed` with `ws` chunks per window, on an input
/// within the parameter size.
pub fn bhp_hash_uncompressed(cs: &mut Cs, input: &Vec<Boolean>, ws: usize) -> Group {
    let mut bits = bits_copy(input);
    while bits.len() % 3 != 0 {
        bits.push(b_const(false));
    }
    let mc = mont_c(cs);
    let mut acc = g_zero();
    let mut w = 0;
    while w * 3 * ws < bits.len() {
        let lo = w * 3 * ws;
        let hi = if lo + 3 * ws < bits.len() { lo + 3 * ws } else { bits.len() };
        let g = bhp_window(cs, &bits, lo, hi, w, ws, &mc);
        acc = g_add(cs, &acc, &g);
        w += 1;
    }
    acc
}

/// BHPHasher::hash_uncompressed of the input bits W1..W`n`, `ws` chunks per
/// window.
pub fn h_bhp_hash_uncompressed(n: usize, ws: usize) -> Cs {
    let mut cs = cs_new();
    let bits = in_bits(&mut cs, n);
    let _ = bhp_hash_uncompressed(&mut cs, &bits, ws);
    cs
}

/// Elligator2::encode on the private input W1.
pub fn h_ell2_encode() -> Cs {
    let mut cs = cs_new();
    let input = f_new(&mut cs);
    let _ = ell2_encode(&mut cs, &input);
    cs
}

// ---------------------------------------------------------------------------
// circuit/algorithms/src/poseidon, with the parameters as inputs.

/// pow.rs on a constant exponent with big-endian bits `e`: square, then
/// multiply when the bit is set.
pub fn f_pow_const(cs: &mut Cs, x: &Field, e: &Vec<bool>) -> Field {
    let mut out = f_of(lc_one());
    let mut i = 0;
    while i < e.len() {
        out = f_square(cs, &out);
        if e[i] {
            out = f_mul(cs, &out, x);
        }
        i += 1;
    }
    out
}

/// The 253 big-endian bits of `k`, as `Field::to_bits_be` of a constant.
fn const_bits_be(k: u64) -> Vec<bool> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < FIELD_BITS {
        let pos = FIELD_BITS - 1 - i;
        out.push(pos < 64 && (k >> pos) & 1 == 1);
        i += 1;
    }
    out
}

pub struct Poseidon {
    pub rate: usize,
    pub domain: Field,
    pub full: usize,
    pub partial: usize,
    pub alpha: Vec<bool>,
    pub ark: Vec<Vec<Field>>,
    pub mds: Vec<Vec<Field>>,
}

fn f_k(k: i128) -> Field {
    f_of(lc_const(k, 0))
}

fn pos_row(ark: bool, i: usize, n: usize) -> Vec<Field> {
    let mut row = Vec::new();
    let mut j = 0;
    while j < n {
        let k = if ark { 7 * i + j + 3 } else { i + 2 * j + 1 };
        row.push(f_k(k as i128));
        j += 1;
    }
    row
}

/// Test parameters: ark[i][j] = 7i + j + 3, mds[i][j] = i + 2j + 1, domain 5.
pub fn pos_test(rate: usize, full: usize, partial: usize, alpha: u64) -> Poseidon {
    let mut ark = Vec::new();
    let mut i = 0;
    while i < full + partial {
        ark.push(pos_row(true, i, rate + 1));
        i += 1;
    }
    let mut mds = Vec::new();
    let mut i = 0;
    while i < rate + 1 {
        mds.push(pos_row(false, i, rate + 1));
        i += 1;
    }
    Poseidon { rate, domain: f_k(5), full, partial, alpha: const_bits_be(alpha), ark, mds }
}

/// Named parameters: `ark[r][i]` is constant `1 + r (rate + 1) + i`,
/// `mds[i][j]` is `1 + (full + partial + i) (rate + 1) + j`, and the domain
/// is `1 + (full + partial + rate + 1) (rate + 1)`.
pub fn pos_named(cs: &mut Cs, rate: usize, full: usize, partial: usize) -> Poseidon {
    let n = rate + 1;
    let mut ark = Vec::new();
    let mut r = 0;
    while r < full + partial {
        ark.push(pos_named_row(cs, 1 + r * n, n));
        r += 1;
    }
    let mut mds = Vec::new();
    let mut i = 0;
    while i < n {
        mds.push(pos_named_row(cs, 1 + (full + partial + i) * n, n));
        i += 1;
    }
    let domain = f_named(cs, (1 + (full + partial + n) * n) as u32);
    Poseidon { rate, domain, full, partial, alpha: const_bits_be(17), ark, mds }
}

fn pos_named_row(cs: &mut Cs, base: usize, n: usize) -> Vec<Field> {
    let mut row = Vec::new();
    let mut j = 0;
    while j < n {
        row.push(f_named(cs, (base + j) as u32));
        j += 1;
    }
    row
}

/// hash_many.rs `apply_ark`.
pub fn pos_apply_ark(p: &Poseidon, st: &Vec<Field>, round: usize) -> Vec<Field> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < st.len() {
        out.push(f_add(&st[i], &p.ark[round][i]));
        i += 1;
    }
    out
}

fn pos_s_box_elem(cs: &mut Cs, p: &Poseidon, x: &Field, apply: bool) -> Field {
    if apply {
        let c = f_of(lc_compact(cs, &x.lc));
        f_pow_const(cs, &c, &p.alpha)
    } else {
        f_copy(x)
    }
}

/// `apply_s_box`: every element in a full round, the first otherwise.
pub fn pos_apply_s_box(cs: &mut Cs, p: &Poseidon, st: &Vec<Field>, full: bool) -> Vec<Field> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < st.len() {
        let e = pos_s_box_elem(cs, p, &st[i], full || i == 0);
        out.push(e);
        i += 1;
    }
    out
}

/// Row `i` of `apply_mds`: the sum of `state[j] * mds[i][j]` from zero.
fn pos_mds_row(cs: &mut Cs, p: &Poseidon, st: &Vec<Field>, i: usize) -> Field {
    let mut acc = f_of(lc_zero());
    let mut j = 0;
    while j < st.len() {
        let t = f_mul(cs, &st[j], &p.mds[i][j]);
        acc = f_add(&acc, &t);
        j += 1;
    }
    f_of(lc_compact(cs, &acc.lc))
}

/// `apply_mds`.
pub fn pos_apply_mds(cs: &mut Cs, p: &Poseidon, st: &Vec<Field>) -> Vec<Field> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < st.len() {
        let e = pos_mds_row(cs, p, st, i);
        out.push(e);
        i += 1;
    }
    out
}

fn pos_round(cs: &mut Cs, p: &Poseidon, st: &Vec<Field>, i: usize) -> Vec<Field> {
    let half = p.full / 2;
    let is_full = !(half <= i && i < half + p.partial);
    let a = pos_apply_ark(p, st, i);
    let b = pos_apply_s_box(cs, p, &a, is_full);
    pos_apply_mds(cs, p, &b)
}

/// `permute`: the partial rounds are the middle `partial` of the rounds.
pub fn pos_permute(cs: &mut Cs, p: &Poseidon, st: &Vec<Field>) -> Vec<Field> {
    let mut s = f_vec_copy(st);
    let mut i = 0;
    while i < p.full + p.partial {
        s = pos_round(cs, p, &s, i);
        i += 1;
    }
    s
}

fn f_vec_copy(x: &Vec<Field>) -> Vec<Field> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < x.len() {
        out.push(f_copy(&x[i]));
        i += 1;
    }
    out
}

/// The sponge state and `DuplexSpongeMode`: `squeezing` with the next index.
pub struct Sponge {
    pub st: Vec<Field>,
    pub squeezing: bool,
    pub index: usize,
}

fn pos_add_elem(st: &Vec<Field>, i: usize, start: usize, input: &Vec<Field>, lo: usize, n: usize) -> Field {
    if start <= i && i < start + n {
        f_add(&st[i], &input[lo + i - start])
    } else {
        f_copy(&st[i])
    }
}

/// `state[start + i] += input[lo + i]` for `i < n`.
fn pos_add_into(st: &Vec<Field>, start: usize, input: &Vec<Field>, lo: usize, n: usize) -> Vec<Field> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < st.len() {
        out.push(pos_add_elem(st, i, start, input, lo, n));
        i += 1;
    }
    out
}

/// The `absorb` loop from absorb index `idx` on `input[lo..]`.
fn pos_absorb_loop(cs: &mut Cs, p: &Poseidon, st: Vec<Field>, idx: usize, input: &Vec<Field>, lo: usize) -> Sponge {
    let remaining = input.len() - lo;
    if idx + remaining <= p.rate {
        let st2 = pos_add_into(&st, 1 + idx, input, lo, remaining);
        Sponge { st: st2, squeezing: false, index: idx + remaining }
    } else {
        let n = p.rate - idx;
        let st2 = pos_add_into(&st, 1 + idx, input, lo, n);
        let st3 = pos_permute(cs, p, &st2);
        pos_absorb_loop(cs, p, st3, 0, input, lo + n)
    }
}

/// hash_many.rs `absorb` (CAPACITY 1).
pub fn pos_absorb(cs: &mut Cs, p: &Poseidon, s: Sponge, input: &Vec<Field>) -> Sponge {
    if input.len() == 0 {
        s
    } else if s.squeezing || s.index == p.rate {
        let st = pos_permute(cs, p, &s.st);
        pos_absorb_loop(cs, p, st, 0, input, 0)
    } else {
        pos_absorb_loop(cs, p, s.st, s.index, input, 0)
    }
}

fn pos_take(st: &Vec<Field>, from: usize, k: usize, out: Vec<Field>) -> Vec<Field> {
    let mut o = out;
    let mut i = 0;
    while i < k {
        o.push(f_copy(&st[from + i]));
        i += 1;
    }
    o
}

/// The sponge after squeezing, and the outputs.
pub struct Squeezed {
    pub s: Sponge,
    pub out: Vec<Field>,
}

/// The `squeeze_internal` loop from squeeze index `idx` for `n` outputs.
fn pos_squeeze_loop(cs: &mut Cs, p: &Poseidon, st: Vec<Field>, idx: usize, n: usize, out: Vec<Field>) -> Squeezed {
    if idx + n <= p.rate {
        let o = pos_take(&st, 1 + idx, n, out);
        Squeezed { s: Sponge { st, squeezing: true, index: idx + n }, out: o }
    } else {
        let k = p.rate - idx;
        let o = pos_take(&st, 1 + idx, k, out);
        let st2 = pos_permute(cs, p, &st);
        pos_squeeze_loop(cs, p, st2, 0, n - k, o)
    }
}

/// `squeeze_internal`.
pub fn pos_squeeze_internal(cs: &mut Cs, p: &Poseidon, s: Sponge, n: usize) -> Squeezed {
    if !s.squeezing || s.index == p.rate {
        let st = pos_permute(cs, p, &s.st);
        pos_squeeze_loop(cs, p, st, 0, n, Vec::new())
    } else {
        pos_squeeze_loop(cs, p, s.st, s.index, n, Vec::new())
    }
}

/// `squeeze`: no work for zero outputs.
pub fn pos_squeeze(cs: &mut Cs, p: &Poseidon, s: Sponge, n: usize) -> Squeezed {
    if n == 0 {
        Squeezed { s, out: Vec::new() }
    } else {
        pos_squeeze_internal(cs, p, s, n)
    }
}

/// HashMany::hash_many.
pub fn pos_hash_many(cs: &mut Cs, p: &Poseidon, input: &Vec<Field>, n: usize) -> Vec<Field> {
    let mut pre = Vec::new();
    pre.push(f_copy(&p.domain));
    pre.push(f_k(input.len() as i128));
    while pre.len() < p.rate {
        pre.push(f_of(lc_zero()));
    }
    let mut i = 0;
    while i < input.len() {
        pre.push(f_copy(&input[i]));
        i += 1;
    }
    let mut st = Vec::new();
    let mut j = 0;
    while j < p.rate + 1 {
        st.push(f_of(lc_zero()));
        j += 1;
    }
    let s = Sponge { st, squeezing: false, index: 0 };
    let s2 = pos_absorb(cs, p, s, &pre);
    pos_squeeze(cs, p, s2, n).out
}

/// Poseidon with `rate`, `full`, `partial` and alpha 17 on inputs W1..: 0 permute
/// of a state W1..W(rate+1); 1 hash_many of `nin` inputs to `nout` outputs;
/// 2 absorb `nin` inputs into a state W1..W(rate+1) in mode (`sq`, `idx`),
/// then squeeze `nout`; 3 hash_to_scalar of `nin` inputs (hash.rs `hash` is
/// `hash_many(input, 1)[0]`, then `Scalar::from_field_lossy`); 4 `Inject::new`
/// (constant parameters, no constraint). 5 and 6 are 1 and 3 with the
/// named parameters of `pos_named`.
pub fn h_poseidon(op: u32, rate: usize, full: usize, partial: usize, nin: usize, nout: usize, sq: bool, idx: usize) -> Cs {
    let mut cs = cs_new();
    let p = if op >= 5 { pos_named(&mut cs, rate, full, partial) } else { pos_test(rate, full, partial, 17) };
    if op == 0 {
        let st = in_fields(&mut cs, rate + 1);
        let _ = pos_permute(&mut cs, &p, &st);
    } else if op == 1 {
        let xs = in_fields(&mut cs, nin);
        let _ = pos_hash_many(&mut cs, &p, &xs, nout);
    } else if op == 2 {
        let st = in_fields(&mut cs, rate + 1);
        let xs = in_fields(&mut cs, nin);
        let s = Sponge { st, squeezing: sq, index: idx };
        let s2 = pos_absorb(&mut cs, &p, s, &xs);
        let _ = pos_squeeze(&mut cs, &p, s2, nout);
    } else if op == 5 {
        let xs = in_fields(&mut cs, nin);
        let _ = pos_hash_many(&mut cs, &p, &xs, nout);
    } else if op == 3 || op == 6 {
        let xs = in_fields(&mut cs, nin);
        let h = pos_hash_many(&mut cs, &p, &xs, 1);
        let bits = f_to_bits_le(&mut cs, &h[0]);
        let _ = s_from_bits_le(&mut cs, &bits_range(&bits, 0, SCALAR_DATA_BITS));
    }
    cs
}

// ---------------------------------------------------------------------------
// circuit/algorithms/src/keccak. A lane is the 64 little-endian bits of a
// U64; U64 `^`, `&` and `!` act bit by bit (types/integers xor.rs, and.rs,
// not.rs), and `U64::from_bits_le` of 64 bits copies them.

const KECCAK_RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];

fn lane_xor(cs: &mut Cs, x: &Vec<Boolean>, y: &Vec<Boolean>) -> Vec<Boolean> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < x.len() {
        out.push(b_xor(cs, &x[i], &y[i]));
        i += 1;
    }
    out
}

fn lane_and_not(cs: &mut Cs, b: &Vec<Boolean>, c: &Vec<Boolean>) -> Vec<Boolean> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < b.len() {
        let nb = b_not(&b[i]);
        out.push(b_and(cs, &nb, &c[i]));
        i += 1;
    }
    out
}

fn lane_const(k: u64) -> Vec<Boolean> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < 64 {
        out.push(b_const((k >> i) & 1 == 1));
        i += 1;
    }
    out
}

/// hash.rs `rotate_left`: `bits_le.rotate_left(n)`.
pub fn kec_rotate_left(x: &Vec<Boolean>, n: usize) -> Vec<Boolean> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < 64 {
        out.push(b_copy(&x[(i + n) % 64]));
        i += 1;
    }
    out
}

/// `rotl_offsets`: the left rotation of lane x + 5y, (64 - (t + 1)(t + 2) / 2)
/// mod 64 for the lane reached at step t of (x, y) -> (y, 2x + 3y) from (1, 0).
const KECCAK_ROTL: [usize; 25] = [
    0, 63, 2, 36, 37, 28, 20, 58, 9, 44, 61, 54, 21, 39, 25, 23, 19, 49, 43, 56, 46, 62, 3, 8, 50,
];

/// The target lane of pi for the lane `i` = x + 5y: y + 5((2x + 3y) mod 5).
fn kec_pi_target(i: usize) -> usize {
    let x = i % 5;
    let y = i / 5;
    y + 5 * ((2 * x + 3 * y) % 5)
}

/// The source lane of pi for the target lane `t`, searched from lane `i`.
fn kec_pi_source(t: usize, i: usize) -> usize {
    if i >= 24 || kec_pi_target(i) == t {
        i
    } else {
        kec_pi_source(t, i + 1)
    }
}

fn kec_theta_c(cs: &mut Cs, a: &Vec<Vec<Boolean>>, x: usize) -> Vec<Boolean> {
    let t1 = lane_xor(cs, &a[x], &a[x + 5]);
    let t2 = lane_xor(cs, &t1, &a[x + 10]);
    let t3 = lane_xor(cs, &t2, &a[x + 15]);
    lane_xor(cs, &t3, &a[x + 20])
}

fn kec_chi_lane(cs: &mut Cs, a2: &Vec<Vec<Boolean>>, x: usize, y: usize) -> Vec<Boolean> {
    let t = lane_and_not(cs, &a2[(x + 1) % 5 + 5 * y], &a2[(x + 2) % 5 + 5 * y]);
    lane_xor(cs, &a2[x + 5 * y], &t)
}

/// hash.rs `round` on 25 lanes with round constant `rc`.
pub fn kec_round(cs: &mut Cs, a: &Vec<Vec<Boolean>>, rc: u64) -> Vec<Vec<Boolean>> {
    let mut c = Vec::new();
    let mut x = 0;
    while x < 5 {
        c.push(kec_theta_c(cs, a, x));
        x += 1;
    }
    let mut d = Vec::new();
    let mut x = 0;
    while x < 5 {
        let r = kec_rotate_left(&c[(x + 1) % 5], 63);
        d.push(lane_xor(cs, &c[(x + 4) % 5], &r));
        x += 1;
    }
    let mut a1 = Vec::new();
    let mut i = 0;
    while i < 25 {
        a1.push(lane_xor(cs, &a[i], &d[i % 5]));
        i += 1;
    }
    let mut a2 = Vec::new();
    let mut t = 0;
    while t < 25 {
        let s = kec_pi_source(t, 0);
        a2.push(kec_rotate_left(&a1[s], KECCAK_ROTL[s]));
        t += 1;
    }
    let mut a3 = Vec::new();
    let mut i = 0;
    while i < 25 {
        a3.push(kec_chi_lane(cs, &a2, i % 5, i / 5));
        i += 1;
    }
    let first = lane_xor(cs, &a3[0], &lane_const(rc));
    let mut out = Vec::new();
    out.push(first);
    let mut i = 1;
    while i < 25 {
        out.push(bits_copy(&a3[i]));
        i += 1;
    }
    out
}

/// `permutation_f` with the first `rounds` round constants (snarkVM uses 24).
pub fn kec_permutation(cs: &mut Cs, s: &Vec<Boolean>, rounds: usize) -> Vec<Boolean> {
    let mut a = Vec::new();
    let mut i = 0;
    while i < 25 {
        a.push(bits_range(s, 64 * i, 64 * i + 64));
        i += 1;
    }
    let mut r = 0;
    while r < rounds {
        a = kec_round(cs, &a, KECCAK_RC[r]);
        r += 1;
    }
    let mut out = Vec::new();
    let mut i = 0;
    while i < 25 {
        out = bits_append(&out, &a[i]);
        i += 1;
    }
    out
}

/// hash.rs `pad_keccak` (`sha3` false) and `pad_sha3`: constant bits only.
pub fn kec_pad(input: &Vec<Boolean>, bitrate: usize, sha3: bool) -> Vec<Vec<Boolean>> {
    let mut p = bits_append(input, &Vec::new());
    while p.len() % 8 != 0 {
        p.push(b_const(false));
    }
    if sha3 {
        p.push(b_const(false));
        p.push(b_const(true));
        p.push(b_const(true));
        p.push(b_const(false));
    } else {
        p.push(b_const(true));
    }
    while p.len() % bitrate != bitrate - 1 {
        p.push(b_const(false));
    }
    p.push(b_const(true));
    let mut out = Vec::new();
    let mut lo = 0;
    while lo < p.len() {
        out.push(bits_range(&p, lo, lo + bitrate));
        lo += bitrate;
    }
    out
}

fn kec_absorb_block(cs: &mut Cs, s: &Vec<Boolean>, block: &Vec<Boolean>) -> Vec<Boolean> {
    let mut out = Vec::new();
    let mut j = 0;
    while j < s.len() {
        if j < block.len() {
            out.push(b_xor(cs, &s[j], &block[j]));
        } else {
            out.push(b_copy(&s[j]));
        }
        j += 1;
    }
    kec_permutation(cs, &out, 24)
}

/// hash.rs `Keccak::<TYPE, VARIANT>::hash` for VARIANT at most the bitrate
/// (256, 384 and 512), so the squeezing loop never runs.
pub fn kec_hash(cs: &mut Cs, input: &Vec<Boolean>, variant: usize, sha3: bool) -> Vec<Boolean> {
    let bitrate = 1600 - 2 * variant;
    let mut s = Vec::new();
    let mut i = 0;
    while i < 1600 {
        s.push(b_const(false));
        i += 1;
    }
    let blocks = kec_pad(input, bitrate, sha3);
    let mut k = 0;
    while k < blocks.len() {
        s = kec_absorb_block(cs, &s, &blocks[k]);
        k += 1;
    }
    bits_range(&s, 0, variant)
}

/// collections kary_merkle_tree/helpers/path_hash.rs for Keccak: `hash` of
/// constant true followed by the children's bits. `arity` children of
/// `variant` bits W1..W(arity * variant); `sha3` selects SHA-3.
pub fn h_keccak_hash_children(arity: usize, variant: usize, sha3: bool) -> Cs {
    let mut cs = cs_new();
    let children = in_bits(&mut cs, arity * variant);
    let mut input = Vec::new();
    input.push(b_const(true));
    let input2 = bits_append(&input, &children);
    let _ = kec_hash(&mut cs, &input2, variant, sha3);
    cs
}

/// Keccak on a state W1..W1600: 0 `round` with round constant `r`;
/// 1 `permutation_f` with the first `r` round constants; 2 `pad_keccak` and
/// 3 `pad_sha3` of the first `r` bits at bitrate 1088.
pub fn h_keccak(op: u32, r: usize) -> Cs {
    let mut cs = cs_new();
    let s = in_bits(&mut cs, 1600);
    if op >= 2 {
        let _ = kec_pad(&bits_range(&s, 0, r), 1088, op == 3);
    } else if op == 0 {
        let mut a = Vec::new();
        let mut i = 0;
        while i < 25 {
            a.push(bits_range(&s, 64 * i, 64 * i + 64));
            i += 1;
        }
        let _ = kec_round(&mut cs, &a, KECCAK_RC[r]);
    } else {
        let _ = kec_permutation(&mut cs, &s, r);
    }
    cs
}

pub fn h_bh_new(variant: usize) -> Cs {
    let mut cs = cs_new();
    let _ = bh_new(&mut cs, variant);
    cs
}

// ---------------------------------------------------------------------------
// circuit/types/string/src/identifier_literal. An IdentifierLiteral is its
// 31 bytes as 248 little-endian bits.

const IL_BYTES: usize = 31;
const IL_BITS: usize = 248;

/// mod.rs `validate_byte`, with `ByteValidationData::new` and the
/// `is_invalid_*_offset` helpers inlined. Returns the null flag.
pub fn il_validate_byte(cs: &mut Cs, bits: &Vec<Boolean>, first: bool) -> Boolean {
    let b0 = b_copy(&bits[0]);
    let b1 = b_copy(&bits[1]);
    let b2 = b_copy(&bits[2]);
    let b3 = b_copy(&bits[3]);
    let b4 = b_copy(&bits[4]);
    let b5 = b_copy(&bits[5]);
    let b6 = b_copy(&bits[6]);
    let b7 = b_copy(&bits[7]);
    env_assert_eq(cs, &b7.lc, &lc_zero());
    let b4b3 = b_and(cs, &b4, &b3);
    let b1b0 = b_and(cs, &b1, &b0);
    let sum = f_add(
        &f_add(&f_add(&f_add(&f_from_boolean(&b0), &f_from_boolean(&b1)), &f_from_boolean(&b2)), &f_from_boolean(&b3)),
        &f_from_boolean(&b4),
    );
    let all_zero_5 = f_is_equal(cs, &sum, &f_of(lc_zero()));
    let null = b_and(cs, &b_not(&b6), &b_not(&b5));
    let lower = b_and(cs, &b6, &b5);
    let upper_lc = lc_sub(&b6.lc, &lower.lc);
    let digit_lc = lc_sub(&b5.lc, &lower.lc);
    let any_low5 = b_not(&all_zero_5);
    enforce(cs, lc_copy(&null.lc), any_low5.lc, lc_zero());
    let b2_or_b1 = b_or(cs, &b2, &b1);
    let invalid_digit = b_and(cs, &b3, &b2_or_b1);
    enforce(cs, digit_lc, lc_add(&lc_sub(&lc_one(), &b4.lc), &invalid_digit.lc), lc_zero());
    let xor_b2_b1b0 = b_xor(cs, &b2, &b1b0);
    let bad_upper = b_and(cs, &b4b3, &xor_b2_b1b0);
    enforce(cs, upper_lc, lc_add(&all_zero_5.lc, &bad_upper.lc), lc_zero());
    let b2_or_b1b0 = b_or(cs, &b2, &b1b0);
    let bad_lower = b_and(cs, &b4b3, &b2_or_b1b0);
    enforce(cs, lc_copy(&lower.lc), lc_add(&all_zero_5.lc, &bad_lower.lc), lc_zero());
    if first {
        il_first_byte_letter(cs, &b4b3, &b1b0, &b2, &b6);
    }
    null
}

fn il_first_byte_letter(cs: &mut Cs, b4b3: &Boolean, b1b0: &Boolean, b2: &Boolean, b6: &Boolean) {
    let partial = b_and(cs, b4b3, b1b0);
    let is_underscore_offset = b_and(cs, &partial, b2);
    let is_letter = b_and(cs, b6, &b_not(&is_underscore_offset));
    env_assert(cs, &is_letter.lc);
}

/// mod.rs `validate_trailing_nulls`.
pub fn il_validate_trailing_nulls(cs: &mut Cs, nulls: &Vec<Boolean>) {
    let mut i = 1;
    while i < nulls.len() {
        let not_null = b_not(&nulls[i]);
        enforce(cs, lc_copy(&nulls[i - 1].lc), not_null.lc, lc_zero());
        i += 1;
    }
}

/// mod.rs `validate_identifier_bits` (and `validate_identifier_bytes`).
pub fn il_validate_bits(cs: &mut Cs, bits: &Vec<Boolean>) {
    let mut nulls = Vec::new();
    let mut i = 0;
    while i < IL_BYTES {
        let byte = bits_range(bits, 8 * i, 8 * i + 8);
        let null = il_validate_byte(cs, &byte, i == 0);
        nulls.push(null);
        i += 1;
    }
    il_validate_trailing_nulls(cs, &nulls);
}

/// helpers/from_bits.rs `from_bits_le`: excess bits asserted zero, padding
/// with constant false, then `from_bytes`.
pub fn il_from_bits_le(cs: &mut Cs, bits: &Vec<Boolean>) -> Vec<Boolean> {
    if bits.len() > IL_BITS {
        b_assert_bits_are_zero(cs, &bits_range(bits, IL_BITS, bits.len()));
    }
    let mut out = bits_range(bits, 0, IL_BITS);
    while out.len() < IL_BITS {
        out.push(b_const(false));
    }
    il_validate_bits(cs, &out);
    out
}

pub fn il_from_bits_be(cs: &mut Cs, bits: &Vec<Boolean>) -> Vec<Boolean> {
    il_from_bits_le(cs, &bits_rev(bits))
}

/// helpers/from_field.rs.
pub fn il_from_field(cs: &mut Cs, f: &Field) -> Vec<Boolean> {
    let bits = f_to_bits_le(cs, f);
    il_from_bits_le(cs, &bits)
}

/// helpers/to_field.rs: `Field::from_bits_le` of the 248 bits.
pub fn il_to_field(cs: &mut Cs, il: &Vec<Boolean>) -> Field {
    f_from_bits_le(cs, il)
}

/// mod.rs `Inject::new`: `U8::new` of each byte, then `from_bytes`.
pub fn il_new(cs: &mut Cs) -> Vec<Boolean> {
    let mut bits = Vec::new();
    let mut i = 0;
    while i < IL_BITS {
        bits.push(b_new(cs));
        i += 1;
    }
    il_validate_bits(cs, &bits);
    bits
}

// ---------------------------------------------------------------------------
// circuit/program

/// The patched `Scalar::new` (snarkVM-scalar-new-range-check.patch): a
/// variable scalar calls `to_bits_le`, which caches the bits.
pub fn s_new_patched(cs: &mut Cs) -> Field {
    let s = f_new(cs);
    let bits = s_to_bits_le(cs, &s);
    f_cache_bits(&s, &bits)
}

const GENERATOR_X: [u64; 4] = [0x137e82844bbe49c5, 0xe7608833a9dd83f3, 0x16b294b80d905006, 0x036824eb02475007];
const GENERATOR_Y: [u64; 4] = [0xd50dce7d8bcda9d4, 0x7f6758f4c08bc255, 0x37c0a81e810abce5, 0x11b1d8d5c1d897a3];

pub fn g_generator() -> Group {
    Group {
        x: f_const_bits(&limbs_bits(&GENERATOR_X, FIELD_BITS)),
        y: f_const_bits(&limbs_bits(&GENERATOR_Y, FIELD_BITS)),
    }
}

/// Literal type codes: 0 address, 1 boolean, 2 field, 3 group, 4 integer
/// (width `tw`, signedness `ts`), 5 scalar, 6 identifier literal.
fn p_zero_or_one(cs: &mut Cs, x: &Field) {
    let is_one = f_is_one(cs, x);
    let is_zero = f_is_zero(cs, x);
    let r = b_or(cs, &is_zero, &is_one);
    env_assert(cs, &r.lc);
}

/// cast/field.rs.
pub fn p_field_cast(cs: &mut Cs, x: &Field, to: u32, tw: usize, ts: bool) {
    if to == 0 || to == 3 {
        let _ = g_from_x_coordinate(cs, x);
    } else if to == 1 {
        p_zero_or_one(cs, x);
    } else if to == 4 {
        let _ = i_from_field(cs, x, tw, ts);
    } else if to == 5 {
        let bits = f_to_bits_le(cs, x);
        let _ = s_from_bits_le(cs, &bits);
    } else if to == 6 {
        let _ = il_from_field(cs, x);
    }
}

/// cast/boolean.rs and cast_lossy/boolean.rs.
pub fn p_boolean_cast(cs: &mut Cs, b: &Boolean, to: u32, tw: usize, ts: bool) {
    if to == 0 || to == 3 {
        let _ = g_ternary(cs, b, &g_generator(), &g_zero());
    } else if to == 4 {
        let _ = i_ternary(cs, b, &i_const_small(tw, 1, ts), &i_const_small(tw, 0, ts));
    } else if to == 5 {
        let _ = f_ternary(cs, b, &f_of(lc_one()), &f_of(lc_zero()));
    } else if to == 6 {
        let f = f_from_boolean(b);
        let _ = il_from_field(cs, &f);
    }
}

fn p_assert_eq_msb(cs: &mut Cs, msb: &Boolean, bits: &Vec<Boolean>, lo: usize, hi: usize) {
    let mut j = lo;
    while j < hi {
        env_assert_eq(cs, &msb.lc, &bits[j].lc);
        j += 1;
    }
}

fn p_sign_extend(bits: &Vec<Boolean>, n: usize) -> Vec<Boolean> {
    let msb = b_copy(&bits[bits.len() - 1]);
    let mut out = bits_copy(bits);
    while out.len() < n {
        out.push(b_copy(&msb));
    }
    out
}

/// cast/integer.rs, the Integer destination.
pub fn p_int_cast_int(cs: &mut Cs, x: &Integer, tw: usize, ts: bool) {
    let n0 = x.bits.len();
    let s0 = x.signed;
    if !s0 && !ts {
        let _ = i_from_bits_le(cs, &x.bits, tw, ts);
    } else if !s0 && ts {
        if n0 < tw {
            let _ = i_from_bits_le(cs, &x.bits, tw, ts);
        } else {
            b_assert_bits_are_zero(cs, &bits_range(&x.bits, tw - 1, n0));
            let _ = i_from_bits_le(cs, &bits_range(&x.bits, 0, tw), tw, ts);
        }
    } else if s0 && !ts {
        if n0 <= tw {
            let not_msb = b_not(&x.bits[n0 - 1]);
            env_assert(cs, &not_msb.lc);
            let _ = i_from_bits_le(cs, &x.bits, tw, ts);
        } else {
            b_assert_bits_are_zero(cs, &bits_range(&x.bits, tw, n0));
            let _ = i_from_bits_le(cs, &bits_range(&x.bits, 0, tw), tw, ts);
        }
    } else if n0 <= tw {
        let _ = i_from_bits_le(cs, &p_sign_extend(&x.bits, tw), tw, ts);
    } else {
        let msb = b_copy(&x.bits[n0 - 1]);
        p_assert_eq_msb(cs, &msb, &x.bits, tw - 1, n0 - 1);
        let mut lower = bits_range(&x.bits, 0, tw - 1);
        lower.push(msb);
        let _ = i_from_bits_le(cs, &lower, tw, ts);
    }
}

/// cast/integer.rs.
pub fn p_integer_cast(cs: &mut Cs, x: &Integer, to: u32, tw: usize, ts: bool) {
    if to == 1 {
        let is_one = i_is_one(cs, x);
        let is_zero = i_is_zero(cs, x);
        let r = b_or(cs, &is_zero, &is_one);
        env_assert(cs, &r.lc);
    } else if to == 4 {
        p_int_cast_int(cs, x, tw, ts);
    } else if to == 5 {
        let _ = s_from_bits_le(cs, &x.bits);
    } else if to != 2 {
        let f = i_to_field(cs, x);
        p_field_cast(cs, &f, to, tw, ts);
    } else {
        let _ = i_to_field(cs, x);
    }
}

/// cast/scalar.rs. Scalar::is_one / is_zero are Field::is_equal on the field.
pub fn p_scalar_cast(cs: &mut Cs, s: &Field, to: u32, tw: usize, ts: bool) {
    if to == 4 {
        let bits = s_to_bits_le(cs, s);
        let _ = i_from_bits_le(cs, &bits, tw, ts);
    } else if to != 2 && to != 5 {
        p_field_cast(cs, s, to, tw, ts);
    }
}

/// cast/identifier.rs.
pub fn p_idlit_cast(cs: &mut Cs, il: &Vec<Boolean>, to: u32, tw: usize, ts: bool) {
    if to != 2 && to != 6 {
        let f = il_to_field(cs, il);
        p_field_cast(cs, &f, to, tw, ts);
    }
}

/// Source codes as the destination codes; an integer source has width `fw`
/// and signedness `fs`. The input is W1 (boolean, field, scalar), the bits
/// W1..W`fw` (integer) or the 248 bits W1..W248 (identifier literal).
pub fn h_p_cast(from: u32, fw: usize, fs: bool, to: u32, tw: usize, ts: bool) -> Cs {
    let mut cs = cs_new();
    if from == 1 {
        let b = b_var(new_var(&mut cs));
        p_boolean_cast(&mut cs, &b, to, tw, ts);
    } else if from == 2 {
        let x = f_new(&mut cs);
        p_field_cast(&mut cs, &x, to, tw, ts);
    } else if from == 4 {
        let x = in_int(&mut cs, fw, fs);
        p_integer_cast(&mut cs, &x, to, tw, ts);
    } else if from == 5 {
        let s = s_new(&mut cs);
        p_scalar_cast(&mut cs, &s, to, tw, ts);
    } else {
        let il = in_bits(&mut cs, IL_BITS);
        p_idlit_cast(&mut cs, &il, to, tw, ts);
    }
    cs
}

/// 0 Identifier::is_equal, 1 is_not_equal (W1, W2); 2 ProgramID::is_equal,
/// 3 is_not_equal (name W1, network W2; name W3, network W4); 4
/// DynamicFuture::is_equal, 5 is_not_equal (W1..W4; W5..W8).
pub fn h_p_equal(op: u32) -> Cs {
    let mut cs = cs_new();
    if op <= 1 {
        let x = f_new(&mut cs);
        let y = f_new(&mut cs);
        if op == 0 {
            let _ = f_is_equal(&mut cs, &x, &y);
        } else {
            let _ = f_is_not_equal(&mut cs, &x, &y);
        }
    } else if op <= 3 {
        let xn = f_new(&mut cs);
        let xw = f_new(&mut cs);
        let yn = f_new(&mut cs);
        let yw = f_new(&mut cs);
        if op == 2 {
            let a = f_is_equal(&mut cs, &xn, &yn);
            let b = f_is_equal(&mut cs, &xw, &yw);
            let _ = b_and(&mut cs, &a, &b);
        } else {
            let a = f_is_not_equal(&mut cs, &xn, &yn);
            let b = f_is_not_equal(&mut cs, &xw, &yw);
            let _ = b_or(&mut cs, &a, &b);
        }
    } else {
        let r = p_dynamic_future_is_equal(&mut cs);
        if op == 5 {
            let _ = b_not(&r);
        }
    }
    cs
}

fn p_dynamic_future_is_equal(cs: &mut Cs) -> Boolean {
    let xn = f_new(cs);
    let xw = f_new(cs);
    let xf = f_new(cs);
    let xc = f_new(cs);
    let yn = f_new(cs);
    let yw = f_new(cs);
    let yf = f_new(cs);
    let yc = f_new(cs);
    let a = f_is_equal(cs, &xn, &yn);
    let b = f_is_equal(cs, &xw, &yw);
    let ab = b_and(cs, &a, &b);
    let c = f_is_equal(cs, &xf, &yf);
    let abc = b_and(cs, &ab, &c);
    let d = f_is_equal(cs, &xc, &yc);
    b_and(cs, &abc, &d)
}

/// Record::is_hiding: `!version.is_zero()` on the U8 bits W1..W8.
pub fn h_p_record_is_hiding() -> Cs {
    let mut cs = cs_new();
    let v = in_int(&mut cs, 8, false);
    let z = i_is_zero(&mut cs, &v);
    let _ = b_not(&z);
    cs
}

/// response/mod.rs OutputID public, private, external_record, future,
/// dynamic_record and dynamic_future: the expected hash W1, the injected
/// public hash W2 and `assert_eq(W2, W1)`.
pub fn h_p_output_id() -> Cs {
    let mut cs = cs_new();
    let expected = f_new(&mut cs);
    let output = f_new(&mut cs);
    env_assert_eq(&mut cs, &output.lc, &expected.lc);
    cs
}

/// response/mod.rs `OutputID::record`: the expected commitment, checksum and
/// sender ciphertext W1..W3 and their public injections W4..W6.
pub fn h_p_output_id_record() -> Cs {
    let mut cs = cs_new();
    let ec = f_new(&mut cs);
    let ek = f_new(&mut cs);
    let es = f_new(&mut cs);
    let oc = f_new(&mut cs);
    let ok = f_new(&mut cs);
    let os = f_new(&mut cs);
    env_assert_eq(&mut cs, &oc.lc, &ec.lc);
    env_assert_eq(&mut cs, &ok.lc, &ek.lc);
    let is_eq = f_is_equal(&mut cs, &os, &es);
    let is_zero = f_is_zero(&mut cs, &os);
    let ok_sender = b_or(&mut cs, &is_eq, &is_zero);
    env_assert(&mut cs, &ok_sender.lc);
    cs
}

/// network/src/v0.rs `g_scalar_multiply` on the scalar bits `bits_le`; the
/// base `2^i G` has the named coordinates `10000 + 2 i` and `10001 + 2 i`.
pub fn net_g_scalar_multiply(cs: &mut Cs, bits_le: &Vec<Boolean>) -> Group {
    let mut acc = g_zero();
    let mut i = 0;
    while i < bits_le.len() {
        let bx = f_named(cs, (10000 + 2 * i) as u32);
        let by = f_named(cs, (10001 + 2 * i) as u32);
        let sum = g_add(cs, &acc, &Group { x: bx, y: by });
        acc = g_ternary(cs, &bits_le[i], &sum, &acc);
        i += 1;
    }
    acc
}

/// data/record/encrypt.rs `Record::encrypt_symmetric` of a record with no
/// entries: owner W1, W2, nonce W3, W4 and randomizer W5. The encryption
/// domain is the named constant 5000 and the Poseidon8 parameters are those
/// of `pos_named` with `full` and `partial` rounds.
pub fn h_rec_encrypt_symmetric(private_owner: bool, full: usize, partial: usize) -> Cs {
    let mut cs = cs_new();
    let owner = in_group(&mut cs);
    let nonce = in_group(&mut cs);
    let randomizer = s_new(&mut cs);
    let p = pos_named(&mut cs, 8, full, partial);
    let bits = s_to_bits_le(&mut cs, &randomizer);
    let g = net_g_scalar_multiply(&mut cs, &bits);
    env_assert_eq(&mut cs, &nonce.x.lc, &g.x.lc);
    env_assert_eq(&mut cs, &nonce.y.lc, &g.y.lc);
    let view = g_mul_bits(&mut cs, &owner, &bits_rev(&bits));
    let domain = f_named(&mut cs, 5000);
    let mut inputs = Vec::new();
    inputs.push(domain);
    inputs.push(f_copy(&view.x));
    let n = if private_owner { 1 } else { 0 };
    let _ = pos_hash_many(&mut cs, &p, &inputs, n);
    cs
}

/// data/record/decrypt.rs `Record::decrypt` of a record with a public owner
/// and no entries: owner W1, W2, nonce W3, W4 and a fresh view key W5, whose
/// `to_address` reuses the cached scalar bits.
pub fn h_rec_decrypt_public(full: usize, partial: usize) -> Cs {
    let mut cs = cs_new();
    let owner = in_group(&mut cs);
    let nonce = in_group(&mut cs);
    let view_key = s_new(&mut cs);
    let p = pos_named(&mut cs, 8, full, partial);
    let bits = s_to_bits_le(&mut cs, &view_key);
    let view = g_mul_bits(&mut cs, &nonce, &bits_rev(&bits));
    let domain = f_named(&mut cs, 5000);
    let mut inputs = Vec::new();
    inputs.push(domain);
    inputs.push(f_copy(&view.x));
    let _ = pos_hash_many(&mut cs, &p, &inputs, 0);
    let address = net_g_scalar_multiply(&mut cs, &bits);
    env_assert_eq(&mut cs, &address.x.lc, &owner.x.lc);
    env_assert_eq(&mut cs, &address.y.lc, &owner.y.lc);
    cs
}

/// data/literal/mod.rs `Literal::new` in a non-constant mode. `variant`: 0
/// address, 1 boolean, 2 field, 3 group, 4 integer of width `n`, 5 scalar
/// (patched), 6 signature without the compute key's hash_to_scalar, 7
/// identifier literal.
pub fn h_p_literal_new(variant: u32, n: usize, signed: bool) -> Cs {
    let mut cs = cs_new();
    if variant == 0 || variant == 3 {
        let _ = g_new(&mut cs);
    } else if variant == 1 {
        let _ = b_new(&mut cs);
    } else if variant == 2 {
        let _ = f_new(&mut cs);
    } else if variant == 4 {
        let _ = i_new(&mut cs, n, signed);
    } else if variant == 5 {
        let _ = s_new_patched(&mut cs);
    } else if variant == 6 {
        let _ = s_new_patched(&mut cs);
        let _ = s_new_patched(&mut cs);
        let _ = g_new(&mut cs);
        let _ = g_new(&mut cs);
    } else {
        let _ = il_new(&mut cs);
    }
    cs
}

/// IdentifierLiteral harnesses on input bits W1..W`n`: 0 validate_byte of
/// one byte (`first`), 1 validate bits, 2 from_bits_le, 3 from_bits_be.
/// 4 from_field of W1; 5 is_equal and 6 is_not_equal of W1..W248 and
/// W249..W496; 7 validate_trailing_nulls of W1..W`n`.
pub fn h_il(op: u32, n: usize, first: bool) -> Cs {
    let mut cs = cs_new();
    if op == 0 {
        let bits = in_bits(&mut cs, 8);
        let _ = il_validate_byte(&mut cs, &bits, first);
    } else if op == 1 {
        let bits = in_bits(&mut cs, IL_BITS);
        il_validate_bits(&mut cs, &bits);
    } else if op == 2 {
        let bits = in_bits(&mut cs, n);
        let _ = il_from_bits_le(&mut cs, &bits);
    } else if op == 3 {
        let bits = in_bits(&mut cs, n);
        let _ = il_from_bits_be(&mut cs, &bits);
    } else if op == 4 {
        let x = f_new(&mut cs);
        let _ = il_from_field(&mut cs, &x);
    } else if op == 7 {
        let nulls = in_bits(&mut cs, n);
        il_validate_trailing_nulls(&mut cs, &nulls);
    } else {
        let a = in_bits(&mut cs, IL_BITS);
        let b = in_bits(&mut cs, IL_BITS);
        let fa = il_to_field(&mut cs, &a);
        let fb = il_to_field(&mut cs, &b);
        if op == 5 {
            let _ = f_is_equal(&mut cs, &fa, &fb);
        } else {
            let _ = f_is_not_equal(&mut cs, &fa, &fb);
        }
    }
    cs
}
