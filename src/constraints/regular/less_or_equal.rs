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

//! This module provides the implementation of the less or equal constraint.

use crate::prelude::*;

/// This constraint enforce that x <= v
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LessOrEqualConstant {
    /// the constrained variable
    x: Variable,
    /// the value
    v: isize,
}

impl LessOrEqualConstant {
    /// Creates a new instance of a constraint x <= v
    pub fn new(x: Variable, v: isize) -> Self {
        Self { x, v }
    }
}
impl ModelingConstruct for LessOrEqualConstant {
    fn install(&mut self, cp: &mut dyn CpModel) {
        let me = cp.post(Box::new(*self));
        cp.schedule(me)
    }
}
impl Propagator for LessOrEqualConstant {
    fn propagate(&mut self, cp: &mut dyn CpModel) -> CPResult<()> {
        cp.remove_above(self.x, self.v)
    }
}

/// This constraint enforce that x <= y
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LessOrEqualVar {
    /// the constrained variable
    x: Variable,
    /// the value
    y: Variable,
}

impl LessOrEqualVar {
    /// Creates a new instance of a constraint x <= v
    pub fn new(x: Variable, y: Variable) -> Self {
        Self { x, y }
    }
}
impl ModelingConstruct for LessOrEqualVar {
    fn install(&mut self, cp: &mut dyn CpModel) {
        let me = cp.post(Box::new(*self));
        cp.schedule(me);
        cp.propagate_on(me, DomainCondition::MinimumChanged(self.x));
        cp.propagate_on(me, DomainCondition::MaximumChanged(self.x));
        cp.propagate_on(me, DomainCondition::MinimumChanged(self.y));
        cp.propagate_on(me, DomainCondition::MaximumChanged(self.y));
    }
}
impl Propagator for LessOrEqualVar {
    fn propagate(&mut self, cp: &mut dyn CpModel) -> CPResult<()> {
        if cp.is_empty(self.x) || cp.is_empty(self.y) {
            Err(Inconsistency)
        } else {
            cp.remove_above(self.x, cp.max(self.y).unwrap())?;
            cp.remove_below(self.y, cp.min(self.x).unwrap())?;
            Ok(())
        }
    }
}

#[cfg(test)]
mod test_lessorequal_const {
    use crate::prelude::*;

    #[test]
    fn is_sets_the_max() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(10, 20);
        let v = 15;

        cp.install(&mut LessOrEqualConstant::new(x, v));
        assert!(cp.fixpoint().is_ok());
        assert_eq!(Some(15), cp.max(x));
    }
}
#[cfg(test)]
mod test_lessorequal_var {
    use crate::prelude::*;

    #[test]
    fn x_imposes_its_min_when_least_at_install() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(12, 15);
        let y = cp.new_int_var(10, 20);

        cp.install(&mut LessOrEqualVar::new(x, y));
        assert!(cp.fixpoint().is_ok());
        assert_eq!(Some(12), cp.min(y));
    }
    #[test]
    fn x_imposes_its_min_when_least_at_update() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(10, 20);
        let y = cp.new_int_var(10, 20);

        cp.install(&mut LessOrEqualVar::new(x, y));
        assert!(cp.fixpoint().is_ok());

        assert!(cp.remove_below(x, 12).is_ok());
        assert!(cp.fixpoint().is_ok());

        assert_eq!(Some(12), cp.min(y));
    }
    #[test]
    fn y_imposes_its_max_when_least_at_install() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(10, 20);
        let y = cp.new_int_var(10, 15);

        cp.install(&mut LessOrEqualVar::new(x, y));
        assert!(cp.fixpoint().is_ok());
        assert_eq!(Some(15), cp.max(x));
    }
    #[test]
    fn y_imposes_its_max_when_least_at_update() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(10, 20);
        let y = cp.new_int_var(10, 20);

        cp.install(&mut LessOrEqualVar::new(x, y));
        assert!(cp.fixpoint().is_ok());

        assert!(cp.remove_above(y, 15).is_ok());
        assert!(cp.fixpoint().is_ok());

        assert_eq!(Some(15), cp.max(x));
    }
}
