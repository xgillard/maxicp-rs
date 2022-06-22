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

//! This module provides the implementation of the reified is greater or equal
//! constraint.

use crate::prelude::*;

/// This constraint enforce that b <==> (x >= v)
#[derive(Debug, Clone, Copy)]
pub struct IsGreaterOrEqualConstant {
    /// A boolean variable whose value represents the inequality
    b: Variable,
    /// The variable whose inequality is being tested
    x: Variable,
    /// The constant
    v: isize,
}
impl IsGreaterOrEqualConstant {
    /// Creates a new instance of the constaint b <==> (x >= v)
    pub fn new(b: Variable, x: Variable, v: isize) -> Self {
        Self { b, x, v }
    }
}
impl ModelingConstruct for IsGreaterOrEqualConstant {
    fn install(&mut self, cp: &mut dyn CpModel) {
        let me = *self;
        let prop = cp.post(Box::new(me));

        cp.schedule(prop);
        cp.propagate_on(prop, DomainCondition::IsFixed(self.b));
        cp.propagate_on(prop, DomainCondition::MinimumChanged(self.x));
        cp.propagate_on(prop, DomainCondition::MaximumChanged(self.x));
    }
}
impl Propagator for IsGreaterOrEqualConstant {
    fn propagate(&mut self, cp: &mut dyn CpModel) -> CPResult<()> {
        if cp.is_true(self.b) {
            cp.remove_below(self.x, self.v)?;
        } else if cp.is_false(self.b) {
            cp.remove_above(self.x, self.v - 1)?;
        }

        let xmin = cp.min(self.x).unwrap();
        let xmax = cp.max(self.x).unwrap();
        if xmin >= self.v {
            cp.fix_bool(self.b, true)?;
        } else if xmax < self.v {
            cp.fix_bool(self.b, false)?;
        }

        Ok(())
    }
}

/// This constraint enforce that b <==> (x >= v)
#[derive(Debug, Clone, Copy)]
pub struct IsGreaterOrEqualVar {
    /// A boolean variable whose value represents the inequality
    b: Variable,
    /// The first variable whose inequality is being tested
    x: Variable,
    /// The first variable whose inequality is being tested
    y: Variable,
}
impl IsGreaterOrEqualVar {
    /// Creates a new instance of the constaint b <==> (x >= y)
    pub fn new(b: Variable, x: Variable, y: Variable) -> Self {
        Self { b, x, y }
    }
}
impl ModelingConstruct for IsGreaterOrEqualVar {
    fn install(&mut self, cp: &mut dyn CpModel) {
        let me = *self;
        let prop = cp.post(Box::new(me));

        cp.schedule(prop);
        cp.propagate_on(prop, DomainCondition::IsFixed(self.b));
        cp.propagate_on(prop, DomainCondition::MinimumChanged(self.x));
        cp.propagate_on(prop, DomainCondition::MaximumChanged(self.x));
        cp.propagate_on(prop, DomainCondition::MinimumChanged(self.y));
        cp.propagate_on(prop, DomainCondition::MaximumChanged(self.y));
    }
}
impl Propagator for IsGreaterOrEqualVar {
    fn propagate(&mut self, cp: &mut dyn CpModel) -> CPResult<()> {
        let xmin = cp.min(self.x).unwrap();
        let xmax = cp.max(self.x).unwrap();
        let ymin = cp.min(self.y).unwrap();
        let ymax = cp.max(self.y).unwrap();

        if cp.is_true(self.b) {
            cp.remove_below(self.x, ymin)?;
            cp.remove_above(self.y, xmax)?;
        } else if cp.is_false(self.b) {
            cp.remove_above(self.x, ymax - 1)?;
            cp.remove_below(self.y, xmin + 1)?;
        }

        if xmin >= ymax {
            cp.fix_bool(self.b, true)?;
        } else if xmax < ymin {
            cp.fix_bool(self.b, false)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod test_isgreaterorequal_const {
    use crate::prelude::*;

    // if b is true when posted  -> ge is enforced on x
    #[test]
    fn if_b_is_true_on_install_x_ge_v_is_enforced() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 3;

        assert_eq!(Ok(()), cp.fix_bool(b, true));
        cp.install(&mut IsGreaterOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(3), cp.min(x));
    }
    // if b is false when posted -> gt is enforced on x
    #[test]
    fn if_b_is_false_on_install_x_lt_v_is_enforced() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 3;

        assert_eq!(Ok(()), cp.fix_bool(b, false));
        cp.install(&mut IsGreaterOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(2), cp.max(x));
    }
    // when b is open when posted -> it enforces nothing
    #[test]
    fn if_b_is_open_on_install_it_enforces_nothing() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 3;

        cp.install(&mut IsGreaterOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(-10), cp.min(x));
        assert_eq!(Some(10), cp.max(x));
    }

    // if x satisfied when posted -> it enforces b
    #[test]
    fn if_condition_satisfied_on_install_b_must_be_true() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = -20;

        cp.install(&mut IsGreaterOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert!(cp.is_true(b));
    }
    // if x falsifies when posted -> it enforces not b
    #[test]
    fn if_condition_falsified_on_install_b_must_be_false() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 20;

        cp.install(&mut IsGreaterOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert!(cp.is_false(b));
    }
    // when x neither falsifies nor invalidates, then it does nothing
    #[test]
    fn if_condition_open_on_install_b_must_be_open() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 0;

        cp.install(&mut IsGreaterOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(0), cp.min(b));
        assert_eq!(Some(1), cp.max(b));
    }

    // when b is fixed true -> it enforces x <= v
    #[test]
    fn if_b_is_true_on_propagate_condition_must_be_forced() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 0;

        cp.install(&mut IsGreaterOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(0), cp.min(b));
        assert_eq!(Some(1), cp.max(b));
        assert_eq!(Some(-10), cp.min(x));
        assert_eq!(Some(10), cp.max(x));

        assert_eq!(Ok(()), cp.fix_bool(b, true));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(1), cp.min(b));
        assert_eq!(Some(1), cp.max(b));
        assert_eq!(Some(0), cp.min(x));
        assert_eq!(Some(10), cp.max(x));
    }
    // when b is fixed false -> it enforces x > v
    #[test]
    fn if_b_is_false_on_propagate_condition_must_be_made_impossible() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 0;

        cp.install(&mut IsGreaterOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(0), cp.min(b));
        assert_eq!(Some(1), cp.max(b));
        assert_eq!(Some(-10), cp.min(x));
        assert_eq!(Some(10), cp.max(x));

        assert_eq!(Ok(()), cp.fix_bool(b, false));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(0), cp.min(b));
        assert_eq!(Some(0), cp.max(b));
        assert_eq!(Some(-1), cp.max(x));
        assert_eq!(Some(-10), cp.min(x));
    }
    // when x makes be impossible -> b is updated
    #[test]
    fn when_condition_is_impossible_on_propagate_b_must_be_changed() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 0;

        cp.install(&mut IsGreaterOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(0), cp.min(b));
        assert_eq!(Some(1), cp.max(b));
        assert_eq!(Some(-10), cp.min(x));
        assert_eq!(Some(10), cp.max(x));

        assert_eq!(Ok(()), cp.remove_above(x, -1));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(0), cp.min(b));
        assert_eq!(Some(0), cp.max(b));
        assert_eq!(Some(-10), cp.min(x));
        assert_eq!(Some(-1), cp.max(x));
    }
    // when x makes be mandatory  -> b is updated
    #[test]
    fn when_condition_is_forced_on_propagate_b_must_be_changed() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 0;

        cp.install(&mut IsGreaterOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(0), cp.min(b));
        assert_eq!(Some(1), cp.max(b));
        assert_eq!(Some(-10), cp.min(x));
        assert_eq!(Some(10), cp.max(x));

        assert_eq!(Ok(()), cp.remove_below(x, 0));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(1), cp.min(b));
        assert_eq!(Some(1), cp.max(b));
        assert_eq!(Some(0), cp.min(x));
        assert_eq!(Some(10), cp.max(x));
    }
}

#[cfg(test)]
mod test_is_ge_var {
    use crate::prelude::*;

    // when b is true, ymin forces xmin (at install)
    #[test]
    fn when_b_is_true_ymin_forces_xmin_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(0, 20);

        cp.fix_bool(b, true).ok();
        cp.install(&mut IsGreaterOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert_eq!(Some(0), cp.min(x));
    }
    // when b is true, ymin forces xmin (at propag)
    #[test]
    fn when_b_is_true_ymin_forces_ymin_at_propag() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(0, 20);

        cp.install(&mut IsGreaterOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.fix_bool(b, true).ok();
        cp.fixpoint().ok();

        assert_eq!(Some(0), cp.min(x));
    }
    // when b is true, xmax forces ymax (at install)
    #[test]
    fn when_b_is_true_xmax_forces_ymax_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 20);

        cp.fix_bool(b, true).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsGreaterOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert_eq!(Some(10), cp.max(y));
    }
    // when b is true, xmax forces ymax (at propag)
    #[test]
    fn when_b_is_true_xmax_forces_ymax_at_propag() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 20);

        cp.install(&mut IsGreaterOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.fix_bool(b, true).ok();
        cp.fixpoint().ok();

        assert_eq!(Some(10), cp.max(y));
    }

    // when b is false, ymin forces xmax (at install)
    #[test]
    fn when_b_is_false_ymax_forces_xmax_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 0);

        cp.install(&mut IsGreaterOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.fix_bool(b, false).ok();
        cp.fixpoint().ok();

        assert_eq!(Some(-1), cp.max(x));
    }
    // when b is false, ymax forces xmax (at propag)
    #[test]
    fn when_b_is_false_ymax_forces_xmax_at_propag() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 0);

        cp.fix_bool(b, false).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsGreaterOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert_eq!(Some(-1), cp.max(x));
    }
    // when b is false, xmax forces ymin (at install)
    #[test]
    fn when_b_is_false_xmax_forces_ymin_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 20);

        cp.fix_bool(b, false).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsGreaterOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert_eq!(Some(-9), cp.min(y));
    }
    // when b is false, xmax forces ymin (at propag)
    #[test]
    fn when_b_is_false_xmax_forces_ymin_at_propag() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 20);

        cp.install(&mut IsGreaterOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.fix_bool(b, false).ok();
        cp.fixpoint().ok();

        assert_eq!(Some(-9), cp.min(y));
    }

    // b must be true when and xmin >= ymax (install)
    #[test]
    fn b_must_be_true_when_xmin_ge_ymax_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 20);

        cp.remove_below(x, 10).ok();
        cp.remove_above(y, 9).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsGreaterOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert!(cp.is_true(b));
    }
    // b must be true when and xmin >= ymax (propag)
    #[test]
    fn b_must_be_true_when_xmin_ge_ymax_at_propag() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 20);

        cp.install(&mut IsGreaterOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.remove_below(x, 10).ok();
        cp.remove_above(y, 9).ok();
        cp.fixpoint().ok();

        assert!(cp.is_true(b));
    }
    // b must be false when and xmax < ymin (install)
    #[test]
    fn b_must_be_false_when_xmax_lt_ymin_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 20);

        cp.remove_above(x, 0).ok();
        cp.remove_below(y, 1).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsGreaterOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert!(cp.is_false(b));
    }
    // b must be false when and xmax < ymin (propag)
    #[test]
    fn b_must_be_false_when_xmax_lt_ymin_at_propag() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 20);

        cp.install(&mut IsGreaterOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.remove_above(x, 0).ok();
        cp.remove_below(y, 1).ok();
        cp.fixpoint().ok();

        assert!(cp.is_false(b));
    }
}
