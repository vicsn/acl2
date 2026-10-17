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
//! A linear combination is a list of terms `c * 2^sh * v`. Wire `0` is the
//! constant one. As in snarkVM, a linear combination is constant when it has
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
}

pub struct Constraint {
    pub a: Vec<Term>,
    pub b: Vec<Term>,
    pub c: Vec<Term>,
}

pub struct Cs {
    pub next: u32,
    pub cs: Vec<Constraint>,
}

/// BLS12-377 scalar field: `p - 1` and `(p - 1) / 2`, little-endian limbs.
const P_MINUS_ONE: [u64; 4] = [0x0a11800000000000, 0x59aa76fed0000001, 0x60b44d1e5c37b001, 0x12ab655e9a2ca556];
const P_HALF: [u64; 4] = [0x8508c00000000000, 0xacd53b7f68000000, 0x305a268f2e1bd800, 0x0955b2af4d1652ab];
/// `E::BaseField::size_in_bits()` and `size_in_data_bits()`.
const FIELD_BITS: usize = 253;
const FIELD_DATA_BITS: usize = 252;

// ---------------------------------------------------------------------------
// Linear combinations

fn tm(c: i128, sh: u32, v: u32) -> Term {
    Term { c, sh, v }
}

pub fn cs_new() -> Cs {
    Cs { next: 0, cs: Vec::new() }
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
    tm(c, sh, t.v)
}

/// The sum of two terms on the same wire, when it fits in one term.
fn term_merge(x: Term, y: Term) -> (bool, Term) {
    if x.c == 0 {
        (true, y)
    } else if y.c == 0 {
        (true, x)
    } else if x.sh == y.sh {
        (true, term_norm(tm(x.c + y.c, x.sh, x.v)))
    } else if small(x.c) && small(y.c) && x.sh < y.sh && y.sh - x.sh < 56 {
        (true, term_norm(tm(x.c + y.c * pow2(y.sh - x.sh), x.sh, x.v)))
    } else if small(x.c) && small(y.c) && y.sh < x.sh && x.sh - y.sh < 56 {
        (true, term_norm(tm(y.c + x.c * pow2(x.sh - y.sh), y.sh, x.v)))
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
        if !merged && u.v == t.v {
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
        out = lc_push(out, tm(t.c * c, t.sh + sh, t.v));
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
fn lc_mul_const(x: &Vec<Term>, k: &Vec<Term>) -> Vec<Term> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < k.len() {
        out = lc_add(&out, &lc_scale(x, k[i].c, k[i].sh));
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
        f_of(lc_mul_const(&x.lc, &y.lc))
    } else if f_is_const(x) {
        f_of(lc_mul_const(&y.lc, &x.lc))
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
    let inv = if f_is_const(x) { f_of(lc_zero()) } else { f_new(cs) };
    enforce(cs, lc_copy(&x.lc), lc_copy(&inv.lc), lc_one());
    inv
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

/// add_wrapped.rs: the low `n` of `to_lower_bits_le(n + 1)` of the field sum.
pub fn i_add_wrapped(cs: &mut Cs, x: &Integer, y: &Integer) -> Integer {
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
    if x.signed {
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
pub fn i_mul_checked(cs: &mut Cs, x: &Integer, y: &Integer) -> Integer {
    if x.signed {
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
/// 14 mul_checked, 15 karatsuba_multiply.
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
    } else {
        let _ = i_karatsuba_multiply(&mut cs, &x, &y);
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
