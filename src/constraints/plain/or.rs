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

//! This module provides the implementation of the "or" (logical clause)
//! constraint.

use std::{cell::UnsafeCell, rc::Rc};

use crate::prelude::*;

/// This constraint enforces that a logical clause be true.
///
/// Note:
/// The clause imposes an additional invariant; in the vector of literals,
/// all literals are meant to be unique (which does not precludes from using
/// views on the same data)
#[derive(Debug, Clone)]
pub struct Or {
    /// Even though the variables in a CP solver are called variables, in the
    /// case of boolean, these are truly literals. This is why they are stored
    /// as such in the literal vector. A positive literal is nothing but the
    /// variable and negative literal is a view over the posisive one.
    literals: Vec<Variable>,
}

impl Or {
    /// Creates a new instance of the logical or constraint.
    pub fn new(literals: Vec<Variable>) -> Self {
        let mut me = Self { literals };
        me.literals.sort_unstable();
        me.literals.dedup();
        me
    }
}

impl ModelingConstruct for Or {
    fn install(&mut self, cp: &mut CpModel) {
        match self.literals.len() {
            0 => {
                // an empty clause is always false: by definition it is an inconsistency
                let inconsistent = cp.post(Box::new(Self::empty_is_inconsistent));
                cp.schedule(inconsistent);
            }
            1 => {
                // an unit clause amounts to forcing the single literal to be true
                let force = cp.post(Box::new(MustBeTrue::new(self.literals[0])));
                cp.schedule(force);
            }
            _ => {
                // otherwise, just pick any two literals and watch them

                // SAFETY:
                // This unsafe block wont ever create a data race because the
                // boxed clause is heap allocated; hence the actual location of
                // the clause remains fixed and will not move (using an explicit
                // pin might make this intent clearer but it would type-bloat
                // the rest of the code for no benefit)
                unsafe {
                    let shared = Rc::new(UnsafeCell::new(Clause::from(&*self)));
                    let boxed = Box::new(shared.clone());
                    let bcp = cp.post(boxed);
                    (*shared.get()).prop = Some(bcp);

                    cp.schedule(bcp);
                    cp.propagate_on(bcp, DomainCondition::IsFixed(self.literals[0]));
                    cp.propagate_on(bcp, DomainCondition::IsFixed(self.literals[1]));
                }
            }
        }
    }
}

impl Or {
    /// Always yields an inconsistency
    fn empty_is_inconsistent(_cp: &mut CpModel) -> CPResult<()> {
        Err(Inconsistency)
    }
}

/// A clause is the real structure implementing the actual boolean constraint
/// propagation using the two watched literal scheme.
struct Clause {
    /// Even though the variables in a CP solver are called variables, in the
    /// case of boolean, these are truly literals. This is why they are stored
    /// as such in the literal vector. A positive literal is nothing but the
    /// variable and negative literal is a view over the posisive one.
    ///
    /// By convention, the first two literals in the vector are the watched
    /// literals.
    literals: Vec<Variable>,
    /// The identifier of the propagator associated with this constraint (if it
    /// has been posted)
    prop: Option<Constraint>,
}
impl From<&Or> for Clause {
    fn from(from: &Or) -> Self {
        Clause {
            literals: from.literals.clone(),
            prop: None,
        }
    }
}
impl Propagator for Rc<UnsafeCell<Clause>> {
    fn propagate(&mut self, cp: &mut CpModel) -> CPResult<()> {
        unsafe { (*self.get()).propagate(cp) }
    }
}
impl Propagator for Clause {
    fn propagate(&mut self, cp: &mut CpModel) -> CPResult<()> {
        let wl1 = self.satisfiable_watched_literal(cp, 0);
        if !wl1 {
            cp.fix_bool(self.literals[1], true)
        } else {
            let wl2 = self.satisfiable_watched_literal(cp, 1);
            if !wl2 {
                cp.fix_bool(self.literals[0], true)
            } else {
                Ok(())
            }
        }
    }
}
impl Clause {
    /// This is the key to boolean constraint propagation with watched literals.
    /// This method is called to check if there exists a literal that can be
    /// the `wlpos`th watched literal.
    ///
    /// If the current literal is still satisfiable, then the method does nothing
    /// and returns true. However, in the case where a new watched literal needs
    /// to be found, it will iterate over the remaining possible candidates.
    /// In the event where a new WL is found, then this method swaps the position
    /// of the old WL with that of the new and returns true. In the event where
    /// no new WL can be found, the method returns false as a means to tell the
    /// caller that some propagation must occur.
    fn satisfiable_watched_literal(&mut self, cp: &mut CpModel, wlpos: usize) -> bool {
        if cp.is_false(self.literals[wlpos]) {
            let other = self
                .literals
                .iter()
                .copied()
                .enumerate()
                .skip(2)
                .find(|(_, lit)| cp.contains(*lit, 1));

            if let Some((pos, other)) = other {
                self.literals.swap(wlpos, pos);

                if !cp.is_true(other) {
                    cp.propagate_on(self.prop.unwrap(), DomainCondition::IsFixed(other));
                }
                true
            } else {
                false
            }
        } else {
            true
        }
    }
}

#[cfg(test)]
mod tests_or {
    use crate::prelude::*;

    #[test]
    fn empty_clause_is_always_inconsistent() {
        let mut cp = CpModel::default();
        let x = vec![];

        cp.install(&mut Or::new(x));
        assert!(cp.fixpoint().is_err());
    }
    #[test]
    fn unit_clause_always_forces_value() {
        let mut cp = CpModel::default();
        let x = vec![cp.new_bool_var()];

        cp.install(&mut Or::new(x.clone()));
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_true(x[0]));
    }

    #[test]
    fn it_works_fine_with_duplicates() {
        let mut cp = CpModel::default();
        let b = cp.new_bool_var();
        let x = vec![b, b];

        cp.install(&mut Or::new(x));
        assert!(cp.fixpoint().is_ok());

        assert!(cp.fix_bool(b, false).is_err());
    }

    #[test]
    fn or1() {
        let mut cp = CpModel::default();
        let x = vec![
            cp.new_bool_var(),
            cp.new_bool_var(),
            cp.new_bool_var(),
            cp.new_bool_var(),
        ];

        cp.install(&mut Or::new(x.clone()));
        cp.fixpoint().ok();

        for l in x.iter().copied() {
            assert!(!cp.is_fixed(l));
        }
        cp.fix(x[1], 0).ok();
        cp.fix(x[2], 0).ok();
        cp.fix(x[3], 0).ok();
        assert!(cp.fixpoint().is_ok());

        assert!(cp.is_true(x[0]));
    }
    #[test]
    fn or2() {
        let mut cp = CpModel::default();
        let x = vec![
            cp.new_bool_var(),
            cp.new_bool_var(),
            cp.new_bool_var(),
            cp.new_bool_var(),
        ];

        cp.install(&mut Or::new(x.clone()));
        cp.fixpoint().ok();

        for l in x.iter().copied() {
            assert!(!cp.is_fixed(l));
        }
        cp.fix(x[0], 0).ok();
        assert!(cp.fixpoint().is_ok());

        cp.fix(x[1], 0).ok();
        assert!(cp.fixpoint().is_ok());

        cp.fix(x[2], 0).ok();
        assert!(cp.fixpoint().is_ok());

        assert!(cp.fix(x[3], 0).is_err());
    }
}
