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

//! This module provides the implementation of the reified "minimum" constraint.
//! This constraint states that y = minimum(a, b, c, d, e, f, ..)

use crate::prelude::*;

/// This constraint enforces that y = minimum(x[0], x[1], x[2], ...])
#[derive(Debug, Clone)]
pub struct IsMinimum {
    /// The variable whose value must be equal to the minimum value among all xs
    y: Variable,
    /// The set of variables enforcing the value of y
    x: Vec<Variable>,
}

impl IsMinimum {
    /// Creates a new instance of minimum constraint
    pub fn new(y: Variable, mut x: Vec<Variable>) -> Self {
        x.sort_unstable();
        x.dedup();

        Self { y, x }
    }
}
impl ModelingConstruct for IsMinimum {
    fn install(&mut self, cp: &mut CpModel) {
        let prop = cp.post(Box::new(self.clone()));

        cp.schedule(prop);
        cp.propagate_on(prop, DomainCondition::MinimumChanged(self.y));
        cp.propagate_on(prop, DomainCondition::MaximumChanged(self.y));
        for x in self.x.iter().copied() {
            cp.propagate_on(prop, DomainCondition::MinimumChanged(x));
            cp.propagate_on(prop, DomainCondition::MaximumChanged(x));
        }
    }
}
impl Propagator for IsMinimum {
    fn propagate(&mut self, cp: &mut CpModel) -> CPResult<()> {
        let mut min = isize::MAX;
        let mut max = isize::MAX;

        let mut n_support = 0;
        let mut support_var = None;

        // calling the propagator when a variable has an empty domain is a
        // BUG. It is okay to panic in that case.
        let ymin = cp.min(self.y).unwrap();
        let ymax = cp.max(self.y).unwrap();
        for x in self.x.iter().copied() {
            cp.remove_below(x, ymin)?;

            let xmin = cp.min(x).unwrap();
            let xmax = cp.max(x).unwrap();
            min = xmin.min(min);
            max = xmax.min(max);

            if xmin <= ymax {
                n_support += 1;
                support_var = Some(x);
            }
        }
        if n_support == 1 {
            cp.remove_above(support_var.unwrap(), ymax)?;
        }

        cp.remove_below(self.y, min)?;
        cp.remove_above(self.y, max)
    }
}

#[cfg(test)]
mod test_isminimum {
    use crate::prelude::*;

    // the xs impose the lowest minimum as min value for the domain of y
    #[test]
    fn the_xs_impose_their_least_minimum_as_minimum_of_y_at_install() {
        let mut cp = CpModel::default();
        let y = cp.new_int_var(-200, 20);
        let xs = vec![
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(-100, 20),
        ];

        cp.install(&mut IsMinimum::new(y, xs));
        cp.fixpoint().ok();

        assert_eq!(Some(-100), cp.min(y))
    }
    #[test]
    fn the_xs_impose_their_least_minimum_as_minimum_of_y_at_propag() {
        let mut cp = CpModel::default();
        let y = cp.new_int_var(-200, 20);
        let xs = vec![
            cp.new_int_var(-200, 20),
            cp.new_int_var(-200, 20),
            cp.new_int_var(-200, 20),
            cp.new_int_var(-100, 20),
        ];

        cp.install(&mut IsMinimum::new(y, xs.clone()));
        cp.fixpoint().ok();

        for x in xs.iter().copied().take(3) {
            cp.remove_below(x, 10).ok();
        }
        cp.fixpoint().ok();
        assert_eq!(Some(-100), cp.min(y))
    }

    // the xs impose the least maximum as max value for the domain of y
    #[test]
    fn the_xs_impose_their_least_maximum_as_maximum_of_y_at_install() {
        let mut cp = CpModel::default();
        let y = cp.new_int_var(-200, 200);
        let xs = vec![
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 10),
        ];

        cp.install(&mut IsMinimum::new(y, xs));
        cp.fixpoint().ok();

        assert_eq!(Some(10), cp.max(y))
    }
    #[test]
    fn the_xs_impose_their_least_maximum_as_maximum_of_y_at_propag() {
        let mut cp = CpModel::default();
        let y = cp.new_int_var(-200, 200);
        let xs = vec![
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 90),
        ];

        cp.install(&mut IsMinimum::new(y, xs.clone()));
        cp.fixpoint().ok();

        cp.remove_above(xs[3], 20).ok();
        cp.fixpoint().ok();

        assert_eq!(Some(20), cp.max(y))
    }
    // y imposes its maximum as max to all xs
    #[test]
    fn y_imposes_its_minimum_to_all_xs_at_install() {
        let mut cp = CpModel::default();
        let y = cp.new_int_var(-5, 20);
        let xs = vec![
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 40),
        ];

        cp.install(&mut IsMinimum::new(y, xs.clone()));
        cp.fixpoint().ok();

        for x in xs.iter().copied().take(3) {
            assert_eq!(Some(-5), cp.min(x))
        }
    }
    #[test]
    fn y_imposes_its_maximum_to_all_xs_at_propag() {
        let mut cp = CpModel::default();
        let y = cp.new_int_var(-200, 200);
        let xs = vec![
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 40),
        ];

        cp.install(&mut IsMinimum::new(y, xs.clone()));
        cp.fixpoint().ok();

        cp.remove_below(y, 5).ok();
        cp.fixpoint().ok();
        for x in xs.iter().copied().take(3) {
            assert_eq!(Some(5), cp.min(x))
        }
    }

    // y forces the value of its last support
    #[test]
    fn y_imposes_its_value_to_last_support_at_install() {
        let mut cp = CpModel::default();
        let y = cp.new_int_var(7, 7);
        let xs = vec![
            cp.new_int_var(-20, 10),
            cp.new_int_var(20, 35),
            cp.new_int_var(20, 35),
            cp.new_int_var(20, 35),
        ];

        cp.install(&mut IsMinimum::new(y, xs.clone()));
        cp.fixpoint().ok();

        assert!(cp.is_fixed(xs[0]));
        assert_eq!(Some(7), cp.min(xs[0]));
    }

    #[test]
    fn y_imposes_its_value_to_last_support_at_propag() {
        let mut cp = CpModel::default();
        let y = cp.new_int_var(-20, 20);
        let xs = vec![
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
        ];

        cp.install(&mut IsMinimum::new(y, xs.clone()));
        cp.fixpoint().ok();

        cp.remove_below(xs[1], 10).ok();
        cp.remove_below(xs[2], 10).ok();
        cp.remove_below(xs[3], 10).ok();
        cp.fixpoint().ok();

        assert!(!cp.is_fixed(y));
        assert!(!cp.is_fixed(xs[0]));

        cp.fix(y, 7).ok();
        cp.fixpoint().ok();

        assert!(cp.is_fixed(y));
        assert!(cp.is_fixed(xs[0]));

        assert_eq!(Some(7), cp.min(y));
        assert_eq!(Some(7), cp.min(xs[0]));
    }

    // when all x are fixed, y equates to the minimum value among xs
    #[test]
    fn when_all_xs_are_fixed_y_must_equate_to_minimum_among_them_at_install() {
        let mut cp = CpModel::default();
        let y = cp.new_int_var(-200, 200);
        let xs = vec![
            cp.new_int_var(20, 20),
            cp.new_int_var(20, 20),
            cp.new_int_var(5, 5),
            cp.new_int_var(20, 20),
        ];

        cp.install(&mut IsMinimum::new(y, xs.clone()));
        cp.fixpoint().ok();

        assert!(cp.is_fixed(y));
        assert_eq!(Some(5), cp.min(y));
    }
    #[test]
    fn when_all_xs_are_fixed_y_must_equate_to_minimum_among_them_at_propag() {
        let mut cp = CpModel::default();
        let y = cp.new_int_var(-200, 200);
        let xs = vec![
            cp.new_int_var(-10, 20),
            cp.new_int_var(-10, 20),
            cp.new_int_var(-60, 60),
            cp.new_int_var(-10, 20),
        ];

        cp.install(&mut IsMinimum::new(y, xs.clone()));
        cp.fixpoint().ok();

        for x in xs.iter().copied() {
            cp.fix(x, cp.min(x).unwrap()).ok();
        }
        cp.fixpoint().ok();

        assert!(cp.is_fixed(y));
        assert_eq!(Some(-60), cp.min(y));
    }
}
