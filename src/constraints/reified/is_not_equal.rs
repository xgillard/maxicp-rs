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

//! This module provides the implementation of the reified different constraint.

use crate::prelude::*;

/// This constraint enforce that b <==> (x != v)
#[derive(Debug, Clone, Copy)]
pub struct IsNotEqualConstant {
    /// A boolean variable whose value represents the inequality
    b: Variable,
    /// The variable whose equlity is being tested
    x: Variable,
    /// The constant
    v: isize,
}

impl IsNotEqualConstant {
    /// Creates a new instance of the constraint b <==> (x!=v)
    pub fn new(b: Variable, x: Variable, v: isize) -> Self {
        Self { b, x, v }
    }
}
impl ModelingConstruct for IsNotEqualConstant {
    fn install(&mut self, cp: &mut CpModel) {
        let me = cp.post(Box::new(*self));

        cp.schedule(me);
        cp.propagate_on(me, DomainCondition::IsFixed(self.b));
        cp.propagate_on(me, DomainCondition::DomainChanged(self.x));
    }
}
impl Propagator for IsNotEqualConstant {
    fn propagate(&mut self, cp: &mut CpModel) -> CPResult<()> {
        if cp.is_true(self.b) {
            cp.remove(self.x, self.v)
        } else if cp.is_false(self.b) {
            cp.fix(self.x, self.v)
        } else if !cp.contains(self.x, self.v) {
            cp.fix(self.b, 1)
        } else if cp.is_fixed(self.x) {
            cp.remove(self.b, 1)
        } else {
            Ok(())
        }
    }
}

/// This constraint enforce that b <==> (x == y)
#[derive(Debug, Clone, Copy)]
pub struct IsNotEqualVar {
    /// A boolean variable whose value represents the inequality
    b: Variable,
    /// The first variable whose equlity is being tested
    x: Variable,
    /// The second variable whose equlity is being tested
    y: Variable,
}
impl IsNotEqualVar {
    /// Creates a new instance of the constraint b <==> (x==v)
    pub fn new(b: Variable, x: Variable, y: Variable) -> Self {
        Self { b, x, y }
    }
}
impl ModelingConstruct for IsNotEqualVar {
    fn install(&mut self, cp: &mut CpModel) {
        let me = cp.post(Box::new(*self));

        cp.schedule(me);
        cp.propagate_on(me, DomainCondition::IsFixed(self.b));
        cp.propagate_on(me, DomainCondition::IsFixed(self.x));
        cp.propagate_on(me, DomainCondition::IsFixed(self.y));
    }
}
impl Propagator for IsNotEqualVar {
    fn propagate(&mut self, cp: &mut CpModel) -> CPResult<()> {
        let bfixed = cp.is_fixed(self.b);
        let xfixed = cp.is_fixed(self.x);
        let yfixed = cp.is_fixed(self.y);

        // calling this propagator when a domain is empty is a bug !
        let xmin = cp.min(self.x).unwrap();
        let ymin = cp.min(self.y).unwrap();

        match (bfixed, xfixed, yfixed) {
            // boolean + x are fixed
            (true, true, _) => {
                if cp.is_true(self.b) {
                    cp.remove(self.y, xmin)
                } else {
                    cp.fix(self.y, xmin)
                }
            }
            // boolean + y are fixed
            (true, _, true) => {
                if cp.is_true(self.b) {
                    cp.remove(self.x, ymin)
                } else {
                    cp.fix(self.x, ymin)
                }
            }
            // x + y are fixed
            (false, true, true) => cp.fix_bool(self.b, xmin != ymin),
            (_, _, _) => Ok(()),
        }
    }
}
#[cfg(test)]
mod test_isnotequal_constant {
    use crate::prelude::*;

    #[test]
    fn when_b_is_true_x_gets_updated_at_at_propag() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(10, 20);
        let v = 15;

        cp.install(&mut IsNotEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(!cp.is_fixed(b));
        assert!(!cp.is_fixed(x));

        assert!(cp.fix_bool(b, true).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(!cp.is_fixed(x));
        assert!(!cp.contains(x, 15));
    }
    #[test]
    fn when_b_is_true_x_gets_fixed_at_at_install() {
        let mut cp = CpModel::default();
        let b = cp.new_int_var(1, 1);
        let x = cp.new_int_var(10, 20);
        let v = 15;

        cp.install(&mut IsNotEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(!cp.is_fixed(x));
        assert!(!cp.contains(x, 15));
    }
    #[test]
    fn when_b_is_false_v_gets_fixed_at_propag() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(10, 20);
        let v = 15;

        cp.install(&mut IsNotEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(!cp.is_fixed(b));
        assert!(!cp.is_fixed(x));

        assert!(cp.fix_bool(b, false).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(x));
        assert_eq!(Some(v), cp.min(x));
    }
    #[test]
    fn when_b_is_false_v_gets_fixed_at_install() {
        let mut cp = CpModel::default();
        let b = cp.new_int_var(0, 0);
        let x = cp.new_int_var(10, 20);
        let v = 15;

        cp.install(&mut IsNotEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(x));
        assert_eq!(Some(v), cp.min(x));
    }

    #[test]
    fn b_must_be_true_when_x_doesnt_contain_v_at_update() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(10, 20);
        let v = 15;

        cp.install(&mut IsNotEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(!cp.is_fixed(b));
        assert!(!cp.is_fixed(x));

        assert!(cp.remove(x, v).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(!cp.is_fixed(x));
        assert!(cp.is_true(b));
    }
    #[test]
    fn b_must_be_true_when_x_doesnt_contain_v_at_install() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(10, 20);
        let v = 105;

        cp.install(&mut IsNotEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(!cp.is_fixed(x));
        assert!(cp.is_true(b));
    }

    #[test]
    fn b_cant_be_true_when_x_is_fixed_to_v_at_update() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(10, 20);
        let v = 15;

        cp.install(&mut IsNotEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(!cp.is_fixed(b));
        assert!(!cp.is_fixed(x));

        assert!(cp.fix(x, v).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(x));
        assert!(cp.is_false(b));
    }
    #[test]
    fn b_cant_be_true_when_x_is_fixed_to_v_at_install() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(15, 15);
        let v = 15;

        cp.install(&mut IsNotEqualConstant::new(b, x, v));
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(x));
        assert!(cp.is_false(b));
    }
}

#[cfg(test)]
mod test_isnotqual_var {
    use crate::prelude::*;

    #[test]
    fn b_true_and_x_fixed_imply_x_ne_y_at_install() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-15, 15);
        let y = cp.new_int_var(-20, 20);

        cp.fix_bool(b, true).ok();
        cp.fix(x, 5).ok();
        cp.install(&mut IsNotEqualVar::new(b, x, y));
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(x));
        assert!(!cp.is_fixed(y));
        assert!(!cp.contains(y, 5));
    }
    #[test]
    fn b_true_and_x_fixed_imply_x_ne_y_at_propag() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-15, 15);
        let y = cp.new_int_var(-20, 20);

        cp.install(&mut IsNotEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.save_state();
        cp.fix_bool(b, true).ok();
        cp.fix(x, 5).ok();
        cp.fixpoint().ok();

        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(x));
        assert!(!cp.is_fixed(y));
        assert!(!cp.contains(y, 5));
    }
    #[test]
    fn b_false_and_x_fixed_imply_x_eq_y_at_install() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-15, 15);
        let y = cp.new_int_var(-20, 20);

        cp.fix_bool(b, false).ok();
        cp.fix(x, 5).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsNotEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(x));
        assert!(cp.is_fixed(y));
        assert_eq!(Some(5), cp.min(y));
    }
    #[test]
    fn b_false_and_x_fixed_imply_x_eq_y_at_propag() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-15, 15);
        let y = cp.new_int_var(-20, 20);

        cp.install(&mut IsNotEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.save_state();
        cp.fix_bool(b, false).ok();
        cp.fix(x, 5).ok();
        cp.fixpoint().ok();

        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(x));
        assert!(cp.is_fixed(y));
        assert_eq!(Some(5), cp.min(y));
    }
    // b true + y fixed ==> y = x
    #[test]
    fn b_true_and_y_fixed_imply_x_eq_y_at_install() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-15, 15);
        let y = cp.new_int_var(-20, 20);

        cp.save_state();
        cp.fix_bool(b, true).ok();
        cp.fix(y, 5).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsNotEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(y));
        assert!(!cp.is_fixed(x));
        assert!(!cp.contains(x, 5));
    }
    #[test]
    fn b_true_and_y_fixed_imply_x_eq_y_at_propag() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-15, 15);
        let y = cp.new_int_var(-20, 20);

        cp.install(&mut IsNotEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.save_state();
        cp.fix_bool(b, true).ok();
        cp.fix(y, 5).ok();
        cp.fixpoint().ok();

        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(y));
        assert!(!cp.is_fixed(x));
        assert!(!cp.contains(x, 5));
    }
    #[test]
    fn b_false_and_y_fixed_imply_x_eq_y_at_install() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-15, 15);
        let y = cp.new_int_var(-20, 20);

        cp.save_state();
        cp.fix_bool(b, false).ok();
        cp.fix(y, 5).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsNotEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(x));
        assert!(cp.is_fixed(y));
        assert_eq!(Some(5), cp.min(x));
    }
    #[test]
    fn b_false_and_y_fixed_imply_x_eq_y_at_propag() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-15, 15);
        let y = cp.new_int_var(-20, 20);

        cp.install(&mut IsNotEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.save_state();
        cp.fix_bool(b, false).ok();
        cp.fix(y, 5).ok();
        cp.fixpoint().ok();

        assert!(cp.is_fixed(b));
        assert!(cp.is_fixed(x));
        assert!(cp.is_fixed(y));
        assert_eq!(Some(5), cp.min(x));
    }
    #[test]
    fn x_ne_y_implies_b_at_install() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-15, 15);
        let y = cp.new_int_var(-20, 20);

        cp.save_state();
        cp.fix(x, 5).ok();
        cp.fix(y, 7).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsNotEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert!(cp.is_fixed(b));
        assert!(cp.is_true(b));
        assert!(cp.is_fixed(x));
        assert!(cp.is_fixed(y));
    }
    #[test]
    fn x_ne_y_implies_b_at_propag() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-15, 15);
        let y = cp.new_int_var(-20, 20);

        cp.install(&mut IsNotEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.save_state();
        cp.fix(x, 5).ok();
        cp.fix(y, 7).ok();
        cp.fixpoint().ok();

        assert!(cp.is_fixed(b));
        assert!(cp.is_true(b));
        assert!(cp.is_fixed(x));
        assert!(cp.is_fixed(y));
    }
    // x != y ==> b false
    #[test]
    fn x_eq_y_implies_not_b_at_install() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-15, 15);
        let y = cp.new_int_var(-20, 20);

        cp.save_state();
        cp.fix(x, 5).ok();
        cp.fix(y, 5).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsNotEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert!(cp.is_fixed(b));
        assert!(cp.is_false(b));
        assert!(cp.is_fixed(x));
        assert!(cp.is_fixed(y));
    }
    #[test]
    fn x_eq_y_implies_not_b_at_propag() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-15, 15);
        let y = cp.new_int_var(-20, 20);

        cp.install(&mut IsNotEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.save_state();
        cp.fix(x, 5).ok();
        cp.fix(y, 5).ok();
        cp.fixpoint().ok();

        assert!(cp.is_fixed(b));
        assert!(cp.is_false(b));
        assert!(cp.is_fixed(x));
        assert!(cp.is_fixed(y));
    }
}
