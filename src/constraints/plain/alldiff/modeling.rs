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

//! This module provides the implementation of the domain consistent alldiff
//! constraint. The algorithm used to implement that constraint is described
//! in "A filtering algorithm for constraints of difference in CSPs" J-C. Régin,
//! AAAI-94.

use crate::prelude::*;

use super::propagator::VarValueGraph;

/// This constraint enforces that the the value affected to each variable be
/// different from the one affected to all other variables.
#[derive(Debug, Clone)]
pub struct AllDiff {
    /// All these variables must take different values in the solution
    vars: Vec<Variable>,
}
impl AllDiff {
    /// creates a new contraint
    pub fn new(vars: Vec<Variable>) -> Self {
        Self { vars }
    }
}
impl ModelingConstruct for AllDiff {
    fn install(&mut self, cp: &mut CpModel) {
        let propagator = VarValueGraph::new(cp, &self.vars);
        let propagator = Box::new(propagator);
        let propagator = cp.post(propagator);

        cp.schedule(propagator);
        for v in self.vars.iter().copied() {
            cp.propagate_on(propagator, DomainCondition::DomainChanged(v));
        }
    }
}

#[cfg(test)]
mod test_alldiff_dc {
    use crate::prelude::*;

    #[test]
    fn test1() {
        let mut cp = CpModel::default();
        let x = vec![
            cp.new_int_var(0, 4),
            cp.new_int_var(0, 4),
            cp.new_int_var(0, 4),
            cp.new_int_var(0, 4),
            cp.new_int_var(0, 4),
        ];
        cp.install(&mut AllDiff::new(x.clone()));
        cp.fixpoint().ok();

        cp.fix(x[0], 0).ok();
        cp.fixpoint().ok();

        for v in x.iter().skip(1).copied() {
            assert_eq!(4, cp.size(v));
            assert_eq!(Some(1), cp.min(v));
        }
    }

    #[test]
    fn test3() {
        let mut cp = CpModel::default();
        let x = vec![
            ivar(&mut cp, &[1, 2]),
            ivar(&mut cp, &[1, 2]),
            ivar(&mut cp, &[1, 2, 3, 4]),
        ];
        cp.install(&mut AllDiff::new(x.clone()));
        cp.fixpoint().ok();

        cp.fix(x[0], 0).ok();
        cp.fixpoint().ok();

        assert_eq!(2, cp.size(x[2]));
        assert_eq!(Some(3), cp.min(x[2]));
    }

    #[test]
    fn test5() {
        let mut cp = CpModel::default();
        let x = vec![
            ivar(&mut cp, &[1, 2, 3, 4, 5]),
            ivar(&mut cp, &[2]),
            ivar(&mut cp, &[1, 2, 3, 4, 5]),
            ivar(&mut cp, &[1]),
            ivar(&mut cp, &[1, 2, 3, 4, 5, 6]),
            ivar(&mut cp, &[6, 7, 8]),
            ivar(&mut cp, &[3]),
            ivar(&mut cp, &[6, 7, 8, 9]),
            ivar(&mut cp, &[6, 7, 8]),
        ];
        cp.install(&mut AllDiff::new(x.clone()));
        cp.fixpoint().ok();

        assert_eq!(cp.size(x[0]), 2);
        assert_eq!(cp.size(x[2]), 2);
        assert_eq!(cp.min(x[4]), Some(6));
        assert_eq!(cp.min(x[7]), Some(9));
        assert_eq!(cp.min(x[8]), Some(7));
        assert_eq!(cp.max(x[8]), Some(8));
    }

    #[test]
    fn test7() {
        let mut cp = CpModel::default();
        let x = vec![
            ivar(&mut cp, &[3, 4]),
            ivar(&mut cp, &[1]),
            ivar(&mut cp, &[3, 4]),
            ivar(&mut cp, &[0]),
            ivar(&mut cp, &[3, 4, 5]),
            ivar(&mut cp, &[5, 6, 7]),
            ivar(&mut cp, &[2, 9, 10]),
            ivar(&mut cp, &[5, 6, 7, 8]),
            ivar(&mut cp, &[5, 6, 7]),
        ];
        cp.install(&mut AllDiff::new(x.clone()));
        cp.fixpoint().ok();

        assert!(!cp.contains(x[4], 3));
        assert!(!cp.contains(x[4], 4));
        assert!(!cp.contains(x[5], 5));
        assert!(!cp.contains(x[7], 5));
        assert!(!cp.contains(x[7], 6));
        assert!(!cp.contains(x[8], 5));
    }

    #[test]
    fn test8() {
        let mut cp = CpModel::default();
        let x = vec![
            ivar(&mut cp, &[0, 2, 3, 5]),
            ivar(&mut cp, &[4]),
            ivar(&mut cp, &[-1, 1]),
            ivar(&mut cp, &[-4, -2, 0, 2, 3]),
            ivar(&mut cp, &[-1]),
        ];
        cp.install(&mut AllDiff::new(x.clone()));
        cp.fixpoint().ok();

        assert!(!cp.contains(x[2], -1));
    }

    fn ivar(cp: &mut CpModel, val: &[isize]) -> Variable {
        let min = val.first().copied().unwrap();
        let max = val.last().copied().unwrap();
        let var = cp.new_int_var(min, max);

        let mut v = val.iter().copied();
        let mut k = v.next();
        for i in min..=max {
            if Some(i) == k {
                k = v.next();
            } else {
                cp.remove(var, i).ok();
            }
        }
        var
    }
}
