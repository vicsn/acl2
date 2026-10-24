//! The same two circuits in snarkVM's shape: a generic `Environment` impl,
//! a closure passed to `enforce`, and `expect`. This is what
//! `circuit/types/boolean/src/{and,xor}.rs` actually looks like. Kept separate
//! because that shape is outside the ACL2 backend's subset.

#[derive(Clone, Copy)]
pub struct Boolean {
    pub is_constant: bool,
    pub value: bool,
    pub id: u32,
}

#[derive(Clone, Copy)]
pub enum Mode {
    Private,
}

pub trait Environment {
    fn one() -> i32;
    fn zero() -> i32;
    fn new_variable(mode: Mode, value: i32) -> u32;
    fn enforce<F: FnOnce() -> (u32, u32, u32)>(f: F) -> Result<(), &'static str>;
}

pub struct Circuit;

impl Environment for Circuit {
    fn one() -> i32 {
        1
    }
    fn zero() -> i32 {
        0
    }
    fn new_variable(_mode: Mode, _value: i32) -> u32 {
        0
    }
    fn enforce<F: FnOnce() -> (u32, u32, u32)>(_f: F) -> Result<(), &'static str> {
        Ok(())
    }
}

pub fn boolean_and<E: Environment>(this: Boolean, other: Boolean) -> Boolean {
    if this.is_constant {
        if this.value { other } else { this }
    } else if other.is_constant {
        if other.value { this } else { other }
    } else {
        let value = this.value & other.value;
        let witness = if value { E::one() } else { E::zero() };
        let id = E::new_variable(Mode::Private, witness);
        let output = Boolean { is_constant: false, value, id };
        E::enforce(|| (this.id, other.id, output.id)).expect("Boolean AND constraint unsatisfied");
        output
    }
}

pub fn boolean_xor<E: Environment>(this: Boolean, other: Boolean) -> Boolean {
    if this.is_constant {
        if this.value {
            Boolean { is_constant: other.is_constant, value: !other.value, id: other.id }
        } else {
            other
        }
    } else if other.is_constant {
        if other.value {
            Boolean { is_constant: this.is_constant, value: !this.value, id: this.id }
        } else {
            this
        }
    } else {
        let value = this.value ^ other.value;
        let witness = if value { E::one() } else { E::zero() };
        let id = E::new_variable(Mode::Private, witness);
        let output = Boolean { is_constant: false, value, id };
        E::enforce(|| (this.id, other.id, output.id)).expect("Boolean XOR constraint unsatisfied");
        output
    }
}

pub fn run_and(this: Boolean, other: Boolean) -> Boolean {
    boolean_and::<Circuit>(this, other)
}

pub fn run_xor(this: Boolean, other: Boolean) -> Boolean {
    boolean_xor::<Circuit>(this, other)
}
