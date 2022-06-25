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

//! This module provides the implementation of the reified "sum" constraint.

use crate::prelude::*;

/// This constraint enforces that sum(terms) == y
#[derive(Debug, Clone)]
pub struct IsSum {
    y: Variable, 
    terms: Vec<Variable>
}

impl IsSum {
    /// Creates a new instance of the constraint y == sum(terms)
    pub fn new(y: Variable, terms: Vec<Variable>) -> Self {
        Self { y, terms }
    }
}

impl ModelingConstruct for IsSum {
    fn install(&mut self, cp: &mut CpModel) {
        let mut terms = self.terms.clone();
        terms.push(cp.neg(self.y));
        cp.install(&mut Sum::new(terms));
    }
}

#[cfg(test)]
mod test_sum {
    use crate::prelude::*;

    #[test]
    fn sum1() {
        let mut cp = CpModel::default();
        let y = cp.new_int_var(-100, 100);
        let x = vec![
            cp.new_int_var(0, 5),
            cp.new_int_var(1, 5),
            cp.new_int_var(0, 5),
        ];
        cp.install(&mut IsSum::new(y, x));
        cp.fixpoint().ok();

        assert_eq!(Some(1), cp.min(y));
        assert_eq!(Some(15), cp.max(y));
    }

    #[test]
    fn sum2() {
        let mut cp = CpModel::default();
        let y = cp.new_int_var(0, 100);
        let x = vec![
            cp.new_int_var(-5, 5),
            cp.new_int_var(1, 2),
            cp.new_int_var(0, 1),
        ];
        cp.install(&mut IsSum::new(y, x.clone()));
        cp.fixpoint().ok();

        assert_eq!(Some(0-3), cp.min(x[0]));
        assert_eq!(Some(0), cp.min(y));
        assert_eq!(Some(8), cp.max(y));
    }

    #[test]
    fn sum3() {
        let mut cp = CpModel::default();
        let y = cp.new_int_var(5, 5);
        let x = vec![
            cp.new_int_var(-5, 5),
            cp.new_int_var(1, 2),
            cp.new_int_var(0, 1),
        ];

        cp.install(&mut IsSum::new(y, x.clone()));
        cp.fixpoint().ok();

        cp.remove_below(x[0], 1).ok();
        // 1-5 + 1-2 + 0-1 = 5
        cp.fix(x[1], 1).ok();
        // 1-5 + 1 + 0-1 = 5
        cp.fixpoint().ok();

        assert_eq!(Some(3), cp.min(x[0]));
        assert_eq!(Some(4), cp.max(x[0]));
        assert_eq!(Some(0), cp.min(x[2]));
        assert_eq!(Some(1), cp.max(x[2]));   
    }
}