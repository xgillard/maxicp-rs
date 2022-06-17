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

//! This module provides the implementation of the absolute value constraint.

use crate::{
    CPResult, ConstraintStore, DomainStore, Inconsistency, ModelingConstruct, Propagator, Variable,
};

use crate::DomainCondition::*;

/// This constraint enforces that y == |x|
#[derive(Debug, Clone, Copy)]
pub struct Absolute {
    x: Variable,
    y: Variable,
}
impl Absolute {
    /// Creates an absolute value modelling construct. It imposes that y==|x|
    pub fn new(x: Variable, y: Variable) -> Self {
        Self { x, y }
    }
}
impl ModelingConstruct for Absolute {
    fn install(&self, cp: &mut dyn ConstraintStore) {
        let at_post = cp.post(self.at_post());
        let propagate = cp.post(Box::new(*self));

        cp.schedule(at_post);

        cp.propagate_on(propagate, DomainChanged(self.x));
        cp.propagate_on(propagate, DomainChanged(self.y));
    }
}

impl Absolute {
    /// Creates a setup propagator which is only triggered once, when the constraint
    /// is installed
    fn at_post(self) -> Box<dyn Propagator> {
        let y = self.y;
        Box::new(move |cp: &mut dyn DomainStore| {
            cp.remove_below(y, 0)?;
            self.propagate(cp)
        })
    }
}
impl Propagator for Absolute {
    fn propagate(&self, cp: &mut dyn DomainStore) -> CPResult<()> {
        let x = self.x;
        let y = self.y;
        if cp.is_empty(x) || cp.is_empty(y) {
            Err(Inconsistency)
        } else {
            let xmin = cp.min(x).unwrap();
            let xmax = cp.max(x).unwrap();
            let ymin = cp.min(y).unwrap();
            let ymax = cp.max(y).unwrap();

            if xmin == xmax {
                // x is fixed
                cp.fix(y, xmin.abs())?;
            } else if ymin == ymax {
                // y is fixed
                if !cp.contains(x, ymin) {
                    cp.fix(x, -ymin)?;
                } else if !cp.contains(x, -ymin) {
                    cp.fix(x, ymin)?;
                } else {
                    // x can be (y or -y): remove everything except y and -y
                    for v in xmin..=xmax {
                        if v != ymin && v != -ymin {
                            cp.remove(x, v)?;
                        }
                    }
                }
            } else if xmin >= 0 {
                cp.remove_below(y, xmin)?;
                cp.remove_above(y, xmax)?;
                cp.remove_below(x, ymin)?;
                cp.remove_above(x, ymax)?;
            } else if xmax <= 0 {
                cp.remove_below(y, -xmax)?;
                cp.remove_above(y, -xmin)?;
                cp.remove_below(x, -ymax)?;
                cp.remove_above(x, -ymin)?;
            } else {
                let max_abs = xmax.max(-xmin);
                cp.remove_above(y, max_abs)?;
                cp.remove_above(x, ymax)?;
                cp.remove_below(x, -ymax)?;

                while !cp.contains(x, cp.min(y).unwrap()) && !cp.contains(x, -cp.min(y).unwrap()) {
                    cp.remove(y, cp.min(y).unwrap())?;
                }
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod test_absolute {
    use crate::prelude::*;

    #[test]
    fn simple_test_0() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-5, 5);
        let y = cp.new_int_var(-10, 10);

        cp.install(&Absolute::new(x, y));
        assert!(cp.fixpoint().is_ok());

        assert_eq!(Some(0), cp.min(y));
        assert_eq!(Some(5), cp.max(x));
        assert_eq!(11, cp.size(x));

        assert!(cp.remove_above(x, -2).is_ok());
        assert!(cp.fixpoint().is_ok());

        assert_eq!(Some(2), cp.min(y));

        assert!(cp.remove_below(x, -4).is_ok());
        assert!(cp.fixpoint().is_ok());

        assert_eq!(Some(4), cp.max(y));
    }

    #[test]
    fn simple_test_1() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-5, 5);
        let y = cp.new_int_var(-10, 10);

        cp.install(&NotEqualConstant::new(x, 0));
        cp.install(&NotEqualConstant::new(x, 5));
        cp.install(&NotEqualConstant::new(x, -5));

        cp.install(&Absolute::new(x, y));
        assert!(cp.fixpoint().is_ok());

        assert_eq!(Some(1), cp.min(y));
        assert_eq!(Some(4), cp.max(y));
    }

    #[test]
    fn simple_test_2() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-5, 0);
        let y = cp.new_int_var(4, 4);

        cp.install(&Absolute::new(x, y));
        assert!(cp.fixpoint().is_ok());

        assert!(cp.is_fixed(x));
        assert!(cp.is_fixed(y));
        assert_eq!(Some(-4), cp.max(x));
    }

    #[test]
    fn simple_test_3() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(7, 7);
        let y = cp.new_int_var(-1000, 12);

        cp.install(&Absolute::new(x, y));
        assert!(cp.fixpoint().is_ok());

        assert!(cp.is_fixed(x));
        assert!(cp.is_fixed(y));
        assert_eq!(Some(7), cp.max(y));
    }

    #[test]
    fn simple_test_4() {
        let mut cp = DefaultCpModel::default();
        let x = cp.new_int_var(-5, 10);
        let y = cp.new_int_var(-6,  7);

        cp.install(&Absolute::new(x, y));
        assert!(cp.fixpoint().is_ok());
        assert_eq!(Some(7), cp.max(x));
        assert_eq!(Some(-5), cp.min(x));

        cp.install(&NotEqualConstant::new(y, 0));
        cp.install(&LessOrEqualConstant::new(x, 4));
        assert!(cp.fixpoint().is_ok());
        assert_eq!(Some(5), cp.max(y));

        cp.install(&LessOrEqualConstant::new(x, -2));
        assert!(cp.fixpoint().is_ok());
        assert_eq!(Some(2), cp.min(y));

        assert!(cp.remove_below(y, 5).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_fixed(x));
        assert!(cp.is_fixed(y));
    }
}
