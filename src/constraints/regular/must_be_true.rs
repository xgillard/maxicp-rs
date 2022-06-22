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

//! This module provides the implementation of the must be true and must be
//! false constraints.
use crate::prelude::*;

/// This constraint enforce that a boolean variable be true.
#[derive(Debug, Clone, Copy)]
pub struct MustBeTrue {
    x: Variable,
}
impl MustBeTrue {
    /// creates a new instance of the constraint
    pub fn new(x: Variable) -> Self {
        Self { x }
    }
}
impl ModelingConstruct for MustBeTrue {
    fn install(&mut self, cp: &mut dyn CpModel) {
        let c = cp.post(Box::new(*self));
        cp.schedule(c)
    }
}
impl Propagator for MustBeTrue {
    fn propagate(&mut self, cp: &mut dyn CpModel) -> CPResult<()> {
        cp.fix(self.x, 1)
    }
}
/// This constraint enforce that a boolean variable be false.
#[derive(Debug, Clone, Copy)]
pub struct MustBeFalse {
    x: Variable,
}
impl MustBeFalse {
    /// creates a new instance of the constraint
    pub fn new(x: Variable) -> Self {
        Self { x }
    }
}
impl ModelingConstruct for MustBeFalse {
    fn install(&mut self, cp: &mut dyn CpModel) {
        let c = cp.post(Box::new(*self));
        cp.schedule(c)
    }
}
impl Propagator for MustBeFalse {
    fn propagate(&mut self, cp: &mut dyn CpModel) -> CPResult<()> {
        cp.fix(self.x, 0)
    }
}

#[cfg(test)]
mod test_mustbe_truefalse {
    use crate::prelude::*;

    #[test]
    fn must_be_true_forces_a_boolean_value() {
        let mut cp = DefaultCpModel::default();

        let b = cp.new_bool_var();
        cp.install(&mut MustBeTrue::new(b));
        cp.fixpoint().ok();

        assert!(cp.is_true(b))
    }

    #[test]
    fn must_be_false_forces_a_boolean_value() {
        let mut cp = DefaultCpModel::default();

        let b = cp.new_bool_var();
        cp.install(&mut MustBeFalse::new(b));
        cp.fixpoint().ok();

        assert!(cp.is_false(b))
    }
    #[test]
    fn cant_apply_both_constraints_at_once() {
        let mut cp = DefaultCpModel::default();

        let b = cp.new_bool_var();
        cp.install(&mut MustBeTrue::new(b));
        cp.install(&mut MustBeFalse::new(b));
        assert_eq!(Err(Inconsistency), cp.fixpoint())
    }
}
