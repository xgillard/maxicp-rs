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

//! This module provides the implementation of the equal constraint.
use crate::prelude::*;
use crate::DomainCondition::*;

/// This constraint enforce that a variable takes the specified constant. x == v
#[derive(Debug, Clone, Copy)]
pub struct EqualConstant {
    x: Variable,
    v: isize,
}
impl EqualConstant {
    /// Creates a not equal constant modeling construct
    pub fn new(x: Variable, v: isize) -> Self {
        Self { x, v }
    }
}
impl ModelingConstruct for EqualConstant {
    fn install(&self, cp: &mut dyn CpModel) {
        let constraint = cp.post(Box::new(*self));
        cp.schedule(constraint);
    }
}
impl Propagator for EqualConstant {
    fn propagate(&self, cp: &mut dyn CpModel) -> CPResult<()> {
        cp.fix(self.x, self.v)
    }
}

/// This constraint enforce that two variables take the same value
#[derive(Debug, Clone, Copy)]
pub struct EqualVar {
    x: Variable,
    y: Variable,
}
impl EqualVar {
    /// Creates an equal constant modeling construct
    pub fn new(x: Variable, y: Variable) -> Self {
        Self { x, y }
    }
}
impl ModelingConstruct for EqualVar {
    fn install(&self, cp: &mut dyn CpModel) {
        let at_post = cp.post(Box::new(self.at_post()));
        let x_changed = cp.post(Box::new(self.on_x_domain_change()));
        let y_changed = cp.post(Box::new(self.on_y_domain_change()));

        cp.schedule(at_post);
        cp.propagate_on(x_changed, DomainChanged(self.x));
        cp.propagate_on(y_changed, DomainChanged(self.y));
    }
}
impl EqualVar {
    fn at_post(self) -> impl Propagator {
        move |cp: &mut dyn CpModel| {
            if cp.is_fixed(self.x) {
                cp.fix(self.y, cp.min(self.x).unwrap())
            } else if cp.is_fixed(self.y) {
                cp.fix(self.x, cp.min(self.y).unwrap())
            } else {
                self.bounds_intersect(cp)?;
                Self::prune_equals(self.x, self.y, cp)?;
                Self::prune_equals(self.y, self.x, cp)?;
                Ok(())
            }
        }
    }

    fn on_x_domain_change(self) -> impl Propagator {
        move |dom: &mut dyn CpModel| {
            self.bounds_intersect(dom)?;
            Self::prune_equals(self.x, self.y, dom)?;
            Ok(())
        }
    }
    fn on_y_domain_change(self) -> impl Propagator {
        move |dom: &mut dyn CpModel| {
            self.bounds_intersect(dom)?;
            Self::prune_equals(self.y, self.x, dom)?;
            Ok(())
        }
    }

    fn bounds_intersect(self, cp: &mut dyn CpModel) -> CPResult<()> {
        if cp.is_empty(self.x) || cp.is_empty(self.y) {
            Err(Inconsistency)
        } else {
            let xmin = cp.min(self.x).unwrap();
            let xmax = cp.max(self.x).unwrap();
            let ymin = cp.min(self.x).unwrap();
            let ymax = cp.max(self.y).unwrap();

            let min = xmin.max(ymin);
            let max = xmax.min(ymax);
            cp.remove_below(self.x, min)?;
            cp.remove_below(self.y, min)?;
            cp.remove_above(self.x, max)?;
            cp.remove_above(self.y, max)?;
            Ok(())
        }
    }

    // dom consistent filtering in the direction from -> to
    // every value of to has a support in from
    fn prune_equals(from: Variable, to: Variable, cp: &mut dyn CpModel) -> CPResult<()> {
        // we could get rid of the allocation at each call, but it would require
        // to either restructure the code, or make 'drop' be a mutable static
        // variable. In that case, the mutation introduces potential dataraces
        // which means the function would have to be marked unsafe.
        let mut drop: Vec<isize> = vec![];
        for value in cp.iter(to) {
            if !cp.contains(from, value) {
                drop.push(value);
            }
        }
        for value in drop {
            cp.remove(to, value)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test_equal_const {
    use crate::prelude::*;

    #[test]
    fn it_just_fixes_it() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-7, 7);

        cp.install(&EqualConstant::new(x, 2));
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(x));
        assert_eq!(Some(2), cp.min(x));
    }
}

#[cfg(test)]
mod test_equal_var {
    use crate::prelude::*;

    fn assert_equal_dom(cp: &dyn DomainStore, x: Variable, y: Variable) {
        cp.iter(x)
            .zip(cp.iter(y))
            .for_each(|(a, b)| assert_eq!(a, b))
    }

    #[test]
    fn test_x_fixed_at_post() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(10, 10);
        let y = cp.new_int_var(0, 10);

        cp.install(&EqualVar::new(x, y));
        assert!(cp.fixpoint().is_ok());
        assert_equal_dom(&cp, x, y);
        assert!(cp.is_fixed(x));
        assert!(cp.is_fixed(y));
        assert_eq!(Some(10), cp.min(x));
        assert_eq!(Some(10), cp.min(y));
    }

    #[test]
    fn test_y_fixed_at_post() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(0, 10);
        let y = cp.new_int_var(10, 10);

        cp.install(&EqualVar::new(x, y));
        assert!(cp.fixpoint().is_ok());
        assert_equal_dom(&cp, x, y);
        assert!(cp.is_fixed(x));
        assert!(cp.is_fixed(y));
        assert_eq!(Some(10), cp.min(x));
        assert_eq!(Some(10), cp.min(y));
    }

    #[test]
    fn test_1() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(0, 10);
        let y = cp.new_int_var(0, 10);

        cp.install(&EqualVar::new(x, y));
        assert!(cp.fixpoint().is_ok());

        assert!(cp.remove_above(x, 7).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert_equal_dom(&cp, x, y);

        assert!(cp.remove_above(y, 6).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert_equal_dom(&cp, x, y);

        assert!(cp.remove(x, 3).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert_equal_dom(&cp, x, y);

        assert!(cp.fix(x, 1).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert_equal_dom(&cp, x, y);
    }

    #[test]
    fn test_2() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(isize::MAX - 20, isize::MAX - 1);
        let y = cp.new_int_var(isize::MAX - 10, isize::MAX - 1);

        cp.install(&NotEqualConstant::new(x, isize::MAX - 5));
        cp.install(&EqualVar::new(x, y));
        assert!(cp.fixpoint().is_ok());
        assert_equal_dom(&cp, x, y);

        cp.install(&EqualConstant::new(x, isize::MAX - 1));
        assert!(cp.fixpoint().is_ok());
        assert_equal_dom(&cp, x, y);

        assert!(cp.is_fixed(x));
        assert_eq!(Some(isize::MAX - 1), cp.min(x));
    }
}
