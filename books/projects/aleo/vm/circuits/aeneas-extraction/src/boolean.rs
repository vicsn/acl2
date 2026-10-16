//! Variable-mode Boolean AND and XOR, the two smallest snarkVM circuits that
//! emit a constraint.
//!
//! Control flow follows `circuit/types/boolean/src/and.rs` (`bitand_assign`)
//! and `xor.rs` (`bitxor_assign`) at snarkVM `7dc117d45`. Constant operands
//! short-circuit on the host and emit nothing. The variable/variable arm
//! records the R1CS triple those functions pass to `E::enforce`:
//!
//! - AND: `(self) * (other) = (output)`
//! - XOR: `(2*self) * (other) = (self + other - output)`
//!
//! The trait, the `||` closure, and `LinearCombination` are gone: this
//! backend skips trait method calls and lambdas. Each linear combination is
//! at most three `(coeff, var)` terms. Var `0` is the field one.

pub struct Term {
    pub coeff: i32,
    pub var: u32,
}

pub struct Lc {
    pub n: u32,
    pub t0: Term,
    pub t1: Term,
    pub t2: Term,
}

pub struct Constraint {
    pub a: Lc,
    pub b: Lc,
    pub c: Lc,
}

pub enum MaybeConstraint {
    None,
    Some(Constraint),
}

/// A boolean wire. `negated` is snarkVM's variable NOT, which is the linear
/// form `1 - wire` and emits no constraint (`not.rs`).
pub struct Boolean {
    pub is_constant: bool,
    pub value: bool,
    pub id: u32,
    pub negated: bool,
}

pub struct AndResult {
    pub output: Boolean,
    pub constraint: MaybeConstraint,
}

pub struct XorResult {
    pub output: Boolean,
    pub constraint: MaybeConstraint,
}

fn mk_term(coeff: i32, var: u32) -> Term {
    Term { coeff, var }
}

fn lc1(coeff: i32, var: u32) -> Lc {
    Lc {
        n: 1,
        t0: mk_term(coeff, var),
        t1: mk_term(0, 0),
        t2: mk_term(0, 0),
    }
}

fn lc3(c0: i32, v0: u32, c1: i32, v1: u32, c2: i32, v2: u32) -> Lc {
    Lc {
        n: 3,
        t0: mk_term(c0, v0),
        t1: mk_term(c1, v1),
        t2: mk_term(c2, v2),
    }
}

fn not_boolean(b: Boolean) -> Boolean {
    Boolean {
        is_constant: b.is_constant,
        value: !b.value,
        id: b.id,
        negated: if b.is_constant { false } else { !b.negated },
    }
}

/// `(self AND other)`. `fresh` is the private witness wire allocated by
/// `E::new_variable` in the variable/variable arm.
pub fn boolean_and(this: Boolean, other: Boolean, fresh: u32) -> AndResult {
    if this.is_constant {
        if this.value {
            AndResult { output: other, constraint: MaybeConstraint::None }
        } else {
            AndResult { output: this, constraint: MaybeConstraint::None }
        }
    } else if other.is_constant {
        if other.value {
            AndResult { output: this, constraint: MaybeConstraint::None }
        } else {
            AndResult { output: other, constraint: MaybeConstraint::None }
        }
    } else {
        let value = this.value && other.value;
        let output = Boolean {
            is_constant: false,
            value,
            id: fresh,
            negated: false,
        };
        let constraint = Constraint {
            a: lc1(1, this.id),
            b: lc1(1, other.id),
            c: lc1(1, fresh),
        };
        AndResult {
            output,
            constraint: MaybeConstraint::Some(constraint),
        }
    }
}

/// `(self XOR other)`. Same split as `bitxor_assign`. A constant `true`
/// operand is snarkVM's `!other`.
pub fn boolean_xor(this: Boolean, other: Boolean, fresh: u32) -> XorResult {
    if this.is_constant {
        if this.value {
            XorResult { output: not_boolean(other), constraint: MaybeConstraint::None }
        } else {
            XorResult { output: other, constraint: MaybeConstraint::None }
        }
    } else if other.is_constant {
        if other.value {
            XorResult { output: not_boolean(this), constraint: MaybeConstraint::None }
        } else {
            XorResult { output: this, constraint: MaybeConstraint::None }
        }
    } else {
        // `^` on bool is lowered to a wrapping bitwise op the ACL2 backend rejects.
        let value = this.value != other.value;
        let output = Boolean {
            is_constant: false,
            value,
            id: fresh,
            negated: false,
        };
        // (self + self) * other = self + other - output
        let constraint = Constraint {
            a: lc1(2, this.id),
            b: lc1(1, other.id),
            c: lc3(1, this.id, 1, other.id, -1, fresh),
        };
        XorResult {
            output,
            constraint: MaybeConstraint::Some(constraint),
        }
    }
}
