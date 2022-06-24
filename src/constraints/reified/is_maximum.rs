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

//! This module provides the implementation of the reified "maximum" constraint.
//! This constraint states that y = maximum(a, b, c, d, e, f, ..)

use crate::prelude::*;

/// This constraint enforces that y = maximum(x[0], x[1], x[2], ...])
#[derive(Debug, Clone)]
pub struct IsMaximum {
    /// The variable whose value must be equal to the maximum value among all xs
    y: Variable,
    /// The set of variables enforcing the value of y
    x: Vec<Variable>,
}

impl IsMaximum {
    /// Creates a new instance of maximum constraint
    pub fn new(y: Variable, mut x: Vec<Variable>) -> Self {
        x.sort_unstable();
        x.dedup();

        Self { y, x }
    }
}
impl ModelingConstruct for IsMaximum {
    fn install(&mut self, cp: &mut dyn CpModel) {
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
impl Propagator for IsMaximum {
    fn propagate(&mut self, cp: &mut dyn CpModel) -> CPResult<()> {
        let mut min = isize::MIN;
        let mut max = isize::MIN;

        let mut n_support = 0;
        let mut support_var = None;

        // calling the propagator when a variable has an empty domain is a
        // BUG. It is okay to panic in that case.
        let ymin = cp.min(self.y).unwrap();
        let ymax = cp.max(self.y).unwrap();
        for x in self.x.iter().copied() {
            cp.remove_above(x, ymax)?;

            let xmin = cp.min(x).unwrap();
            let xmax = cp.max(x).unwrap();
            min = xmin.max(min);
            max = xmax.max(max);

            if xmax >= ymin {
                n_support += 1;
                support_var = Some(x);
            }
        }
        if n_support == 1 {
            cp.remove_below(support_var.unwrap(), ymin)?;
        }

        cp.remove_below(self.y, min)?;
        cp.remove_above(self.y, max)
    }
}

#[cfg(test)]
mod test_ismaximum {
    use crate::prelude::*;

    // the xs impose the greatest minimum as min value for the domain of y
    #[test]
    fn the_xs_impose_their_greatest_minimum_as_minimum_of_y_at_install() {
        let mut cp = DefaultCpModel::default();
        let y = cp.new_int_var(-20, 20);
        let xs = vec![
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(10, 20),
        ];

        cp.install(&mut IsMaximum::new(y, xs));
        cp.fixpoint().ok();

        assert_eq!(Some(10), cp.min(y))
    }
    #[test]
    fn the_xs_impose_their_greatest_minimum_as_minimum_of_y_at_propag() {
        let mut cp = DefaultCpModel::default();
        let y = cp.new_int_var(-20, 20);
        let xs = vec![
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
        ];

        cp.install(&mut IsMaximum::new(y, xs.clone()));
        cp.fixpoint().ok();

        cp.remove_below(xs[3], 10).ok();
        cp.fixpoint().ok();
        assert_eq!(Some(10), cp.min(y))
    }

    // the xs impose the greatest maximum as max value for the domain of y
    #[test]
    fn the_xs_impose_their_greatest_maximum_as_maximum_of_y_at_install() {
        let mut cp = DefaultCpModel::default();
        let y = cp.new_int_var(-200, 200);
        let xs = vec![
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 40),
        ];

        cp.install(&mut IsMaximum::new(y, xs));
        cp.fixpoint().ok();

        assert_eq!(Some(40), cp.max(y))
    }
    #[test]
    fn the_xs_impose_their_greatest_maximum_as_maximum_of_y_at_propag() {
        let mut cp = DefaultCpModel::default();
        let y = cp.new_int_var(-200, 200);
        let xs = vec![
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 40),
        ];

        cp.install(&mut IsMaximum::new(y, xs.clone()));
        cp.fixpoint().ok();

        for x in xs.iter().copied().take(3) {
            cp.remove_above(x, 20).ok();
        }
        cp.fixpoint().ok();

        assert_eq!(Some(40), cp.max(y))
    }
    // y imposes its maximum as max to all xs
    #[test]
    fn y_imposes_its_maximum_to_all_xs_at_install() {
        let mut cp = DefaultCpModel::default();
        let y = cp.new_int_var(-200, 20);
        let xs = vec![
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 40),
        ];

        cp.install(&mut IsMaximum::new(y, xs.clone()));
        cp.fixpoint().ok();

        for x in xs.iter().copied().take(3) {
            assert_eq!(Some(20), cp.max(x))
        }
    }
    #[test]
    fn y_imposes_its_maximum_to_all_xs_at_propag() {
        let mut cp = DefaultCpModel::default();
        let y = cp.new_int_var(-200, 200);
        let xs = vec![
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 60),
            cp.new_int_var(-20, 40),
        ];

        cp.install(&mut IsMaximum::new(y, xs.clone()));
        cp.fixpoint().ok();

        cp.remove_above(y, 20).ok();
        cp.fixpoint().ok();
        for x in xs.iter().copied().take(3) {
            assert_eq!(Some(20), cp.max(x))
        }
    }

    // y forces the value of its last support
    #[test]
    fn y_imposes_its_value_to_last_support_at_install() {
        let mut cp = DefaultCpModel::default();
        let y = cp.new_int_var(7, 7);
        let xs = vec![
            cp.new_int_var(-20, 10),
            cp.new_int_var(-20, -15),
            cp.new_int_var(-20, -15),
            cp.new_int_var(-20, -15),
        ];

        cp.install(&mut IsMaximum::new(y, xs.clone()));
        cp.fixpoint().ok();

        assert!(cp.is_fixed(xs[0]));
        assert_eq!(Some(7), cp.min(xs[0]));
    }

    #[test]
    fn y_imposes_its_value_to_last_support_at_propag() {
        let mut cp = DefaultCpModel::default();
        let y = cp.new_int_var(-20, 20);
        let xs = vec![
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
        ];

        cp.install(&mut IsMaximum::new(y, xs.clone()));
        cp.fixpoint().ok();

        cp.remove_above(xs[1], -15).ok();
        cp.remove_above(xs[2], -15).ok();
        cp.remove_above(xs[3], -15).ok();
        cp.fixpoint().ok();

        assert!(!cp.is_fixed(y));
        assert!(!cp.is_fixed(xs[0]));

        assert_eq!(Some(-20), cp.min(y));
        assert_eq!(Some(20), cp.max(xs[0]));

        assert_eq!(Some(-20), cp.min(xs[0]));
        assert_eq!(Some(20), cp.max(xs[0]));

        cp.fix(y, 7).ok();
        cp.fixpoint().ok();

        assert!(cp.is_fixed(y));
        assert!(cp.is_fixed(xs[0]));

        assert_eq!(Some(7), cp.min(y));
        assert_eq!(Some(7), cp.min(xs[0]));
    }

    // when all x are fixed, y equates to the maximum value among xs
    #[test]
    fn when_all_xs_are_fixed_y_must_equate_to_maximum_among_them_at_install() {
        let mut cp = DefaultCpModel::default();
        let y = cp.new_int_var(-200, 200);
        let xs = vec![
            cp.new_int_var(20, 20),
            cp.new_int_var(20, 20),
            cp.new_int_var(60, 60),
            cp.new_int_var(20, 20),
        ];

        cp.install(&mut IsMaximum::new(y, xs.clone()));
        cp.fixpoint().ok();

        assert!(cp.is_fixed(y));
        assert_eq!(Some(60), cp.min(y));
    }
    #[test]
    fn when_all_xs_are_fixed_y_must_equate_to_maximum_among_them_at_propag() {
        let mut cp = DefaultCpModel::default();
        let y = cp.new_int_var(-200, 200);
        let xs = vec![
            cp.new_int_var(-20, 20),
            cp.new_int_var(-20, 20),
            cp.new_int_var(-60, 60),
            cp.new_int_var(-20, 20),
        ];

        cp.install(&mut IsMaximum::new(y, xs.clone()));
        cp.fixpoint().ok();

        for x in xs.iter().copied() {
            cp.fix(x, cp.max(x).unwrap()).ok();
        }
        cp.fixpoint().ok();

        assert!(cp.is_fixed(y));
        assert_eq!(Some(60), cp.min(y));
    }
}
