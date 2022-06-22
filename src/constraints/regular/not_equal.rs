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

//! This module provides the implementation of the different constraint.

use crate::prelude::*;
use crate::DomainCondition::IsFixed;

/// This constraint enforce that a variable take a different value from the
/// specified constant. x != v
#[derive(Debug, Clone, Copy)]
pub struct NotEqualConstant {
    x: Variable,
    v: isize,
}
impl NotEqualConstant {
    /// Creates a not equal constant modeling construct
    pub fn new(x: Variable, v: isize) -> Self {
        Self { x, v }
    }
}
impl ModelingConstruct for NotEqualConstant {
    fn install(&self, cp: &mut dyn CpModel) {
        let constraint = cp.post(Box::new(*self));
        cp.schedule(constraint);
    }
}
impl Propagator for NotEqualConstant {
    fn propagate(&self, cp: &mut dyn CpModel) -> CPResult<()> {
        cp.remove(self.x, self.v)
    }
}

/// This constraint enforce that a variable take a different value from another
/// x != y
#[derive(Debug, Clone, Copy)]
pub struct NotEqualVar {
    x: Variable,
    y: Variable,
}
impl NotEqualVar {
    /// Creates a not equal constant modeling construct
    pub fn new(x: Variable, y: Variable) -> Self {
        Self { x, y }
    }
}
impl ModelingConstruct for NotEqualVar {
    fn install(&self, cp: &mut dyn CpModel) {
        let x_fixed = cp.post(Box::new(self.on_x_fixed()));
        let y_fixed = cp.post(Box::new(self.on_y_fixed()));

        cp.propagate_on(x_fixed, IsFixed(self.x));
        cp.propagate_on(y_fixed, IsFixed(self.y));
    }
}
impl NotEqualVar {
    fn on_x_fixed(self) -> impl Propagator {
        move |dom: &mut dyn CpModel| dom.remove(self.y, dom.min(self.x).unwrap())
    }
    fn on_y_fixed(self) -> impl Propagator {
        move |dom: &mut dyn CpModel| dom.remove(self.x, dom.min(self.y).unwrap())
    }
}

#[cfg(test)]
mod test_notequal_const {
    use crate::prelude::*;

    #[test]
    fn it_removes_the_const_on_install() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(0, 10);

        cp.install(&NotEqualConstant::new(x, 6));
        assert!(cp.fixpoint().is_ok());
        assert!(!cp.contains(x, 6));
    }
}

#[cfg(test)]
mod test_notequal_var {
    use crate::prelude::*;

    #[test]
    fn x_propagates_to_y() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(0, 10);
        let y = cp.new_int_var(0, 10);

        cp.install(&NotEqualVar::new(x, y));
        assert!(cp.fixpoint().is_ok());
        assert_eq!(11, cp.size(x));
        assert_eq!(11, cp.size(y));

        assert!(cp.fix(x, 6).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert!(!cp.contains(y, 6));
    }

    #[test]
    fn y_propagates_to_x() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(0, 10);
        let y = cp.new_int_var(0, 10);

        cp.install(&NotEqualVar::new(x, y));
        assert!(cp.fixpoint().is_ok());
        assert_eq!(11, cp.size(x));
        assert_eq!(11, cp.size(y));

        assert!(cp.fix(y, 6).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert!(!cp.contains(x, 6));
    }
}
