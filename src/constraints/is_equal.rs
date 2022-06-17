//
// maxicp-rs is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License  v3
// as published by the Free Software Foundation.
//
// mini-cp is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY.
// See the GNU Lesser General Public License  for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with mini-cp. If not, see http://www.gnu.org/licenses/lgpl-3.0.en.html
//
// Copyright (c)  2022 by X. Gillard
//

//! This module provides the implementation of the reified equal constraint.

use crate::prelude::*;

/// This constraint enforce that b <==> (x == v)
#[derive(Debug, Clone, Copy)]
pub struct IsEqualConstant {
    /// A boolean variable whose value represents the inequality
    b: Variable,
    /// The variable whose equlity is being tested
    x: Variable,
    /// The constant
    v: isize,
}

impl IsEqualConstant {
    /// Creates a new instance of the constraint b <==> (x==v)
    pub fn new(b: Variable, x: Variable, v: isize) -> Self {
        Self { b, x, v }
    }
}
impl ModelingConstruct for IsEqualConstant {
    fn install(&self, cp: &mut dyn ConstraintStore) {
        let me = cp.post(Box::new(*self));

        cp.schedule(me);
        cp.propagate_on(me, DomainCondition::IsFixed(self.b));
        cp.propagate_on(me, DomainCondition::DomainChanged(self.x));
    }
}
impl Propagator for IsEqualConstant {
    fn propagate(&self, cp: &mut dyn DomainStore) -> CPResult<()> {
        if cp.is_true(self.b) {
            cp.fix(self.x, self.v)
        } else if cp.is_false(self.b) {
            cp.remove(self.x, self.v)
        } else if !cp.contains(self.x, self.v) {
            cp.remove(self.b, 1)
        } else if cp.is_fixed(self.x) {
            cp.fix(self.b, 1)
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod test_isequal {
    use crate::prelude::*;

    #[test]
    fn when_b_is_true_x_gets_fixed_at_at_propag() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(10, 20);
        let v = 15;

        cp.install(&IsEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(!cp.is_fixed(b));
        assert!(!cp.is_fixed(x));

        assert!(cp.fix_bool(b, true).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(x));
        assert_eq!(Some(15), cp.min(x));
    }
    #[test]
    fn when_b_is_true_x_gets_fixed_at_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_int_var(1, 1);
        let x = cp.new_int_var(10, 20);
        let v = 15;

        cp.install(&IsEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(x));
        assert_eq!(Some(15), cp.min(x));
    }
    #[test]
    fn when_b_is_false_v_gets_removed_at_propag() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(10, 20);
        let v = 15;

        cp.install(&IsEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(!cp.is_fixed(b));
        assert!(!cp.is_fixed(x));

        assert!(cp.fix_bool(b, false).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(!cp.is_fixed(x));
        assert!(!cp.contains(x, v));
    }
    #[test]
    fn when_b_is_false_v_gets_removed_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_int_var(0, 0);
        let x = cp.new_int_var(10, 20);
        let v = 15;

        cp.install(&IsEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(!cp.is_fixed(x));
        assert!(!cp.contains(x, v));
    }

    #[test]
    fn b_cant_be_true_when_x_doesnt_contain_v_at_update() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(10, 20);
        let v = 15;

        cp.install(&IsEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(!cp.is_fixed(b));
        assert!(!cp.is_fixed(x));

        assert!(cp.remove(x, v).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(!cp.is_fixed(x));
        assert!(cp.is_false(b));
    }
    #[test]
    fn b_cant_be_true_when_x_doesnt_contain_v_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(10, 20);
        let v = 105;

        cp.install(&IsEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(!cp.is_fixed(x));
        assert!(cp.is_false(b));
    }

    #[test]
    fn b_mut_be_true_when_x_is_fixed_to_v_at_update() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(10, 20);
        let v = 15;

        cp.install(&IsEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(!cp.is_fixed(b));
        assert!(!cp.is_fixed(x));

        assert!(cp.fix(x, v).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(x));
        assert!(cp.is_true(b));
    }
    #[test]
    fn b_mut_be_true_when_x_is_fixed_to_v_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(15, 15);
        let v = 15;

        cp.install(&IsEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(x));
        assert!(cp.is_true(b));
    }
}
