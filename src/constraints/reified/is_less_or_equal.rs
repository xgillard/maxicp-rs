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

//! This module provides the implementation of the reified is less-or-equal
//! constraint.

use crate::prelude::*;

/// This constraint enforce that b <==> (x <= v)
#[derive(Debug, Clone, Copy)]
pub struct IsLessOrEqualConstant {
    /// A boolean variable whose value represents the inequality
    b: Variable,
    /// The variable whose inequality is being tested
    x: Variable,
    /// The constant
    v: isize,
}

impl ModelingConstruct for IsLessOrEqualConstant {
    fn install(&mut self, cp: &mut dyn CpModel) {
        let me = *self;
        let install = cp.post(Box::new(move |d: &mut dyn CpModel| me.at_install(d)));
        let b_fixed = cp.post(Box::new(move |d: &mut dyn CpModel| me.upon_fixed_bool(d)));
        let xmin_up = cp.post(Box::new(move |d: &mut dyn CpModel| me.when_xmin_change(d)));
        let xmax_dn = cp.post(Box::new(move |d: &mut dyn CpModel| me.when_xmax_change(d)));

        cp.schedule(install);
        cp.propagate_on(b_fixed, DomainCondition::IsFixed(self.b));
        cp.propagate_on(xmin_up, DomainCondition::MinimumChanged(self.x));
        cp.propagate_on(xmax_dn, DomainCondition::MaximumChanged(self.x));
    }
}

impl IsLessOrEqualConstant {
    /// Creates a new instance of the constraint b <==> (x<=v)
    pub fn new(b: Variable, x: Variable, v: isize) -> Self {
        Self { b, x, v }
    }
    /// These are the propagation checks that are performed when the constraint
    /// is being posted onto the cp solver
    fn at_install(self, cp: &mut dyn CpModel) -> CPResult<()> {
        if cp.is_true(self.b) {
            cp.remove_above(self.x, self.v)
        } else if cp.is_false(self.b) {
            cp.remove_below(self.x, 1 + self.v)
        } else if cp.max(self.x) <= Some(self.v) {
            cp.fix_bool(self.b, true)
        } else if cp.min(self.x) > Some(self.v) {
            cp.fix_bool(self.b, false)
        } else {
            Ok(())
        }
    }
    /// The propagation is performed whenever the boolean variable is fixed
    /// (its value is guaranteed to either be true or false - not an open {0,1}
    /// domain)
    fn upon_fixed_bool(self, cp: &mut dyn CpModel) -> CPResult<()> {
        if cp.is_true(self.b) {
            cp.remove_above(self.x, self.v)
        } else {
            cp.remove_below(self.x, 1 + self.v)
        }
    }
    /// This propagation is performed whenever the lower bound of the domain
    /// of x has changed
    fn when_xmin_change(self, cp: &mut dyn CpModel) -> CPResult<()> {
        if cp.min(self.x) > Some(self.v) {
            cp.fix_bool(self.b, false)
        } else {
            Ok(())
        }
    }
    /// This propagation is performed whenever the upper bound of the domain
    /// of x has changed
    fn when_xmax_change(self, cp: &mut dyn CpModel) -> CPResult<()> {
        if cp.max(self.x) <= Some(self.v) {
            cp.fix_bool(self.b, true)
        } else {
            Ok(())
        }
    }
}

/// This constraint enforce that b <==> (x <= y)
#[derive(Debug, Clone, Copy)]
pub struct IsLessOrEqualVar {
    /// A boolean variable whose value represents the inequality
    b: Variable,
    /// The first variable whose inequality is being tested
    x: Variable,
    /// The second variable whose inequality is being tested
    y: Variable,
}
impl IsLessOrEqualVar {
    /// Creates a new instance of the constraint b <==> (x<=v)
    pub fn new(b: Variable, x: Variable, y: Variable) -> Self {
        Self { b, x, y }
    }
}
impl ModelingConstruct for IsLessOrEqualVar {
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
impl Propagator for IsLessOrEqualVar {
    fn propagate(&mut self, cp: &mut dyn CpModel) -> CPResult<()> {
        // propagating when a domain is empty is a BUG.
        let xmin = cp.min(self.x).unwrap();
        let xmax = cp.max(self.x).unwrap();
        let ymin = cp.min(self.y).unwrap();
        let ymax = cp.max(self.y).unwrap();

        if cp.is_true(self.b) {
            cp.remove_above(self.x, ymax)?;
            cp.remove_below(self.y, xmin)?;
        } else if cp.is_false(self.b) {
            cp.remove_below(self.x, ymax + 1)?;
            cp.remove_above(self.y, xmin - 1)?;
        }

        if xmax <= ymin {
            cp.fix_bool(self.b, true)?;
        } else if xmin > ymax {
            cp.fix_bool(self.b, false)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test_is_le_const {
    use crate::prelude::*;

    // if b is true when posted  -> le is enforced on x
    #[test]
    fn if_b_is_true_on_install_x_le_v_is_enforced() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 3;

        assert_eq!(Ok(()), cp.fix_bool(b, true));
        cp.install(&mut IsLessOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(3), cp.max(x));
    }
    // if b is false when posted -> gt is enforced on x
    #[test]
    fn if_b_is_false_on_install_x_gt_v_is_enforced() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 3;

        assert_eq!(Ok(()), cp.fix_bool(b, false));
        cp.install(&mut IsLessOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(4), cp.min(x));
    }
    // when b is open when posted -> it enforces nothing
    #[test]
    fn if_b_is_open_on_install_it_enforces_nothing() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 3;

        cp.install(&mut IsLessOrEqualConstant::new(b, x, v));
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
        let v = 20;

        cp.install(&mut IsLessOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert!(cp.is_true(b));
    }
    // if x falsifies when posted -> it enforces not b
    #[test]
    fn if_condition_falsified_on_install_b_must_be_false() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = -20;

        cp.install(&mut IsLessOrEqualConstant::new(b, x, v));
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

        cp.install(&mut IsLessOrEqualConstant::new(b, x, v));
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

        cp.install(&mut IsLessOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(0), cp.min(b));
        assert_eq!(Some(1), cp.max(b));
        assert_eq!(Some(-10), cp.min(x));
        assert_eq!(Some(10), cp.max(x));

        assert_eq!(Ok(()), cp.fix_bool(b, true));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(1), cp.min(b));
        assert_eq!(Some(1), cp.max(b));
        assert_eq!(Some(-10), cp.min(x));
        assert_eq!(Some(0), cp.max(x));
    }
    // when b is fixed false -> it enforces x > v
    #[test]
    fn if_b_is_false_on_propagate_condition_must_be_made_impossible() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 0;

        cp.install(&mut IsLessOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(0), cp.min(b));
        assert_eq!(Some(1), cp.max(b));
        assert_eq!(Some(-10), cp.min(x));
        assert_eq!(Some(10), cp.max(x));

        assert_eq!(Ok(()), cp.fix_bool(b, false));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(0), cp.min(b));
        assert_eq!(Some(0), cp.max(b));
        assert_eq!(Some(1), cp.min(x));
        assert_eq!(Some(10), cp.max(x));
    }
    // when x makes be impossible -> b is updated
    #[test]
    fn when_condition_is_impossible_on_propagate_b_must_be_changed() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 0;

        cp.install(&mut IsLessOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(0), cp.min(b));
        assert_eq!(Some(1), cp.max(b));
        assert_eq!(Some(-10), cp.min(x));
        assert_eq!(Some(10), cp.max(x));

        assert_eq!(Ok(()), cp.remove_below(x, 1));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(0), cp.min(b));
        assert_eq!(Some(0), cp.max(b));
        assert_eq!(Some(1), cp.min(x));
        assert_eq!(Some(10), cp.max(x));
    }
    // when x makes be mandatory  -> b is updated
    #[test]
    fn when_condition_is_forced_on_propagate_b_must_be_changed() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-10, 10);
        let b = cp.new_bool_var();
        let v = 0;

        cp.install(&mut IsLessOrEqualConstant::new(b, x, v));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(0), cp.min(b));
        assert_eq!(Some(1), cp.max(b));
        assert_eq!(Some(-10), cp.min(x));
        assert_eq!(Some(10), cp.max(x));

        assert_eq!(Ok(()), cp.remove_above(x, 0));
        assert_eq!(Ok(()), cp.fixpoint());
        assert_eq!(Some(1), cp.min(b));
        assert_eq!(Some(1), cp.max(b));
        assert_eq!(Some(-10), cp.min(x));
        assert_eq!(Some(0), cp.max(x));
    }
}

#[cfg(test)]
mod test_is_le_var {
    use crate::prelude::*;

    // when b is true, xmin forces ymin (at install)
    #[test]
    fn when_b_is_true_xmin_forces_ymin_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 20);

        cp.fix_bool(b, true).ok();
        cp.install(&mut IsLessOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert_eq!(Some(-10), cp.min(y));
    }
    // when b is true, xmin forces ymin (at propag)
    #[test]
    fn when_b_is_true_xmin_forces_ymin_at_propag() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 20);

        cp.install(&mut IsLessOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.fix_bool(b, true).ok();
        cp.fixpoint().ok();

        assert_eq!(Some(-10), cp.min(y));
    }
    // when b is true, ymax forces xmax (at install)
    #[test]
    fn when_b_is_true_ymax_forces_xmax_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 5);

        cp.fix_bool(b, true).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsLessOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert_eq!(Some(5), cp.max(x));
    }
    // when b is true, ymax forces xmax (at propag)
    #[test]
    fn when_b_is_true_ymax_forces_xmax_at_propag() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 5);

        cp.install(&mut IsLessOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.fix_bool(b, true).ok();
        cp.fixpoint().ok();

        assert_eq!(Some(5), cp.max(x));
    }

    // when b is false, ymax forces xmin (at install)
    #[test]
    fn when_b_is_false_ymax_forces_xmax_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 5);

        cp.install(&mut IsLessOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.fix_bool(b, false).ok();
        cp.fixpoint().ok();

        assert_eq!(Some(6), cp.min(x));
    }
    // when b is false, ymin forces xmin (at propag)
    #[test]
    fn when_b_is_false_ymax_forces_xmax_at_propag() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 5);

        cp.fix_bool(b, false).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsLessOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert_eq!(Some(6), cp.min(x));
    }
    // when b is false, xmin forces ymax (at install)
    #[test]
    fn when_b_is_false_xmin_forces_ymax_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 5);

        cp.fix_bool(b, false).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsLessOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert_eq!(Some(-11), cp.max(y));
    }
    // when b is false, xmin forces ymax (at propag)
    #[test]
    fn when_b_is_false_xmin_forces_ymax_at_propag() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 5);

        cp.install(&mut IsLessOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.fix_bool(b, false).ok();
        cp.fixpoint().ok();

        assert_eq!(Some(-11), cp.max(y));
    }

    // b must be true when and xmax <= ymin (install)
    #[test]
    fn b_must_be_true_when_xmax_le_xmin_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 20);

        cp.remove_below(y, 10).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsLessOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert!(cp.is_true(b));
    }
    // b must be true when and xmax <= ymin (propag)
    #[test]
    fn b_must_be_true_when_xmax_le_xmin_at_propag() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 20);

        cp.install(&mut IsLessOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.remove_below(y, 10).ok();
        cp.fixpoint().ok();

        assert!(cp.is_true(b));
    }
    // b must be false when and xmin > ymax (install)
    #[test]
    fn b_must_be_false_when_xmin_gt_ymax_at_install() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 20);

        cp.remove_above(y, -11).ok();
        cp.fixpoint().ok();

        cp.install(&mut IsLessOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        assert!(cp.is_false(b));
    }
    // b must be false when and xmin > ymax (propag)
    #[test]
    fn b_must_be_false_when_xmin_gt_ymax_at_propag() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = cp.new_int_var(-10, 10);
        let y = cp.new_int_var(-20, 20);

        cp.install(&mut IsLessOrEqualVar::new(b, x, y));
        cp.fixpoint().ok();

        cp.remove_above(y, -11).ok();
        cp.fixpoint().ok();

        assert!(cp.is_false(b));
    }
}
