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
    } else if x.sh < y.sh && y.sh - x.sh < 64 && y.c < 1000000 && y.c > 0 - 1000000 {
        (true, term_norm(tm(x.c + y.c * pow2(y.sh - x.sh), x.sh, x.v)))
    } else if y.sh < x.sh && x.sh - y.sh < 64 && x.c < 1000000 && x.c > 0 - 1000000 {
        (true, term_norm(tm(y.c + x.c * pow2(x.sh - y.sh), y.sh, x.v)))
    } else {
        (false, x)
    }
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
