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

//! This module provides the implementation of the "and" (logical conjunction)
//! constraint.

use std::rc::Rc;

use crate::prelude::*;

/// This constraint enforces that all of the literals be true
#[derive(Debug, Clone)]
pub struct And {
    /// Even though the variables in a CP solver are called variables, in the
    /// case of boolean, these are truly literals. This is why they are stored
    /// as such in the literal vector. A positive literal is nothing but the
    /// variable and negative literal is a view over the posisive one.
    literals: Rc<Vec<Variable>>,
}
impl And {
    /// Creates a new instance of the logical and constraint.
    pub fn new(literals: Vec<Variable>) -> Self {
        Self {
            literals: Rc::new(literals),
        }
    }
}

impl ModelingConstruct for And {
    fn install(&mut self, cp: &mut CpModel) {
        let c = cp.post(Box::new(self.clone()));
        cp.schedule(c)
    }
}
impl Propagator for And {
    fn propagate(&mut self, cp: &mut CpModel) -> CPResult<()> {
        for l in self.literals.iter().copied() {
            cp.fix_bool(l, true)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests_and {
    use crate::prelude::*;

    #[test]
    fn this_constraint_forces_all_literal_true() {
        let mut cp = CpModel::default();
        let x = vec![
            cp.new_bool_var(),
            cp.new_bool_var(),
            cp.new_bool_var(),
            cp.new_bool_var(),
        ];

        cp.install(&mut And::new(x.clone()));
        cp.fixpoint().ok();

        for l in x.iter().copied() {
            assert!(cp.is_true(l));
        }
    }
}
