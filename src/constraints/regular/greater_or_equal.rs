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

//! This module provides the implementation of the greater or equal constraint.

use crate::prelude::*;

/// This constraint enforces that x >= v
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GreaterOrEqualConstant {
    x: Variable,
    v: isize,
}
impl GreaterOrEqualConstant {
    /// Creates a new instance of a constraint x >= v
    pub fn new(x: Variable, v: isize) -> Self {
        Self { x, v }
    }
}
impl ModelingConstruct for GreaterOrEqualConstant {
    fn install(&self, cp: &mut dyn CpModel) {
        let me = cp.post(Box::new(*self));
        cp.schedule(me)
    }
}
impl Propagator for GreaterOrEqualConstant {
    fn propagate(&self, cp: &mut dyn CpModel) -> CPResult<()> {
        cp.remove_below(self.x, self.v)
    }
}
/// This constraint enforces that x >= y
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GreaterOrEqualVar {
    delegate: LessOrEqualVar,
}
impl GreaterOrEqualVar {
    /// Creates a new instance of a constraint x >= y
    pub fn new(x: Variable, y: Variable) -> Self {
        Self {
            delegate: LessOrEqualVar::new(y, x),
        }
    }
}
impl ModelingConstruct for GreaterOrEqualVar {
    fn install(&self, cp: &mut dyn CpModel) {
        self.delegate.install(cp)
    }
}

#[cfg(test)]
mod test_greaterorequal_const {
    use crate::prelude::*;

    #[test]
    fn is_sets_the_min() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(10, 20);
        let v = 15;

        cp.install(&GreaterOrEqualConstant::new(x, v));
        assert!(cp.fixpoint().is_ok());
        assert_eq!(Some(15), cp.min(x));
    }
}
#[cfg(test)]
mod test_greaterorequal_var {
    use crate::prelude::*;

    #[test]
    fn x_imposes_its_max_when_least_at_install() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(10, 15);
        let y = cp.new_int_var(10, 20);

        cp.install(&GreaterOrEqualVar::new(x, y));
        assert!(cp.fixpoint().is_ok());
        assert_eq!(Some(15), cp.max(y));
    }
    #[test]
    fn x_imposes_its_max_when_least_at_update() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(10, 20);
        let y = cp.new_int_var(10, 20);

        cp.install(&GreaterOrEqualVar::new(x, y));
        assert!(cp.fixpoint().is_ok());

        assert!(cp.remove_above(x, 15).is_ok());
        assert!(cp.fixpoint().is_ok());

        assert_eq!(Some(15), cp.max(y));
    }
    #[test]
    fn y_imposes_its_min_when_greatest_at_install() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(10, 20);
        let y = cp.new_int_var(12, 15);

        cp.install(&GreaterOrEqualVar::new(x, y));
        assert!(cp.fixpoint().is_ok());
        assert_eq!(Some(12), cp.min(x));
    }
    #[test]
    fn y_imposes_its_min_when_greatest_at_update() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(10, 20);
        let y = cp.new_int_var(10, 20);

        cp.install(&GreaterOrEqualVar::new(x, y));
        assert!(cp.fixpoint().is_ok());

        assert!(cp.remove_below(y, 12).is_ok());
        assert!(cp.fixpoint().is_ok());

        assert_eq!(Some(12), cp.min(x));
    }
}
