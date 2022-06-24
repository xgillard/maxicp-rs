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

//! This module provides the implementation of the reified "and" (logical
//! conjunction) constraint.

use std::{cell::UnsafeCell, rc::Rc};

use crate::prelude::*;

/// This constraint enforces that a b <==> a logical conjunction be true.
///
/// Note:
/// The clause imposes an additional invariant; in the vector of literals,
/// all literals are meant to be unique (which does not precludes from using
/// views on the same data)
#[derive(Debug, Clone)]
pub struct IsAnd {
    /// The variable that is equivalent to the disjunction of all others
    b: Variable,
    /// Even though the variables in a CP solver are called variables, in the
    /// case of boolean, these are truly literals. This is why they are stored
    /// as such in the literal vector. A positive literal is nothing but the
    /// variable and negative literal is a view over the posisive one.
    literals: Vec<Variable>,
}

impl IsAnd {
    /// Creates a new instance of the logical or constraint.
    pub fn new(b: Variable, literals: Vec<Variable>) -> Self {
        let mut me = Self { b, literals };
        me.literals.sort_unstable();
        me.literals.dedup();
        me
    }
}

impl ModelingConstruct for IsAnd {
    fn install(&mut self, cp: &mut dyn CpModel) {
        match self.literals.len() {
            0 => {
                // an empty conjunction is always true: by definition
                let b = self.b;
                let c = cp.post(Box::new(move |cp: &mut dyn CpModel| cp.fix(b, 1)));
                cp.schedule(c);
            }
            1 => {
                // if it is an unit conjunction b and the single literal are equal
                let b = self.b;
                let x = self.literals[0];

                let fix_x = cp.post(Box::new(move |cp: &mut dyn CpModel| {
                    Self::boolean_equality(x, b, cp)
                }));
                let fix_b = cp.post(Box::new(move |cp: &mut dyn CpModel| {
                    Self::boolean_equality(b, x, cp)
                }));
                cp.schedule(fix_x);
                cp.schedule(fix_b);
                cp.propagate_on(fix_x, DomainCondition::IsFixed(x));
                cp.propagate_on(fix_b, DomainCondition::IsFixed(b));
            }
            _ => {
                // otherwise, just pick any two literals and watch them

                // SAFETY:
                // This unsafe block wont ever create a data race because the
                // boxed conjunction is heap allocated; hence the actual
                // location of the conjunction remains fixed and will not move
                // (using an explicit pin might make this intent clearer but it
                // would type-bloat the rest of the code for no benefit)
                unsafe {
                    let shared = Rc::new(UnsafeCell::new(Conjunction::from(&*self)));
                    let boxed = Box::new(shared.clone());
                    let bcp = cp.post(boxed);
                    (*shared.get()).prop = Some(bcp);

                    cp.schedule(bcp);
                    cp.propagate_on(bcp, DomainCondition::IsFixed(self.b));
                    cp.propagate_on(bcp, DomainCondition::IsFixed(self.literals[0]));
                    cp.propagate_on(bcp, DomainCondition::IsFixed(self.literals[1]));
                }
            }
        }
    }
}
impl IsAnd {
    fn boolean_equality(a: Variable, b: Variable, cp: &mut dyn CpModel) -> CPResult<()> {
        if cp.is_true(a) {
            cp.fix_bool(b, true)
        } else if cp.is_false(a) {
            cp.fix_bool(b, false)
        } else {
            Ok(())
        }
    }
}

/// A conjunction is the real structure implementing the actual boolean constraint
/// propagation using the two watched literal scheme. It is very similar
/// (actually, it is a pure symmetry of the Clause which is implemented for the
/// is_or scheme using De Morgan's Law)
///
/// Note:
/// The conjunction imposes an additional invariant; in the vector of literals,
/// all literals are meant to be unique (which does not precludes from using
/// views on the same data)
struct Conjunction {
    /// The variable that is equivalent to the disjunction of all others
    b: Variable,
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
impl From<&IsAnd> for Conjunction {
    fn from(from: &IsAnd) -> Self {
        Conjunction {
            b: from.b,
            literals: from.literals.clone(),
            prop: None,
        }
    }
}
impl Propagator for Rc<UnsafeCell<Conjunction>> {
    fn propagate(&mut self, cp: &mut dyn CpModel) -> CPResult<()> {
        unsafe { (*self.get()).propagate(cp) }
    }
}
impl Propagator for Conjunction {
    fn propagate(&mut self, cp: &mut dyn CpModel) -> CPResult<()> {
        if cp.is_true(self.b) {
            for l in self.literals.iter().copied() {
                cp.fix_bool(l, true)?;
            }
        } else {
            let wl1 = self.falsifiable_watched_literal(cp, 0);
            let wl2 = self.falsifiable_watched_literal(cp, 1);

            if cp.is_false(self.b) {
                if !wl1 {
                    cp.fix_bool(self.literals[1], false)?;
                } else if !wl2 {
                    cp.fix_bool(self.literals[0], false)?;
                }
            } else if !wl1 && !wl2 {
                cp.fix_bool(self.b, true)?;
            } else {
                // LAZY APPROACH -- A more eager version is possible but
                // it requires to iterate on all literals + post a listener
                // to propagate on all literals. I think this would be
                // too expensive for the benefit it would bring. This lazy
                // approach is more in line with the philosophy of the 2WL
                // scheme -- and what is usually done in sat solvers.
                if cp.is_false(self.literals[0]) || cp.is_false(self.literals[1]) {
                    cp.fix_bool(self.b, false)?;
                }
            }
        }
        Ok(())
    }
}
impl Conjunction {
    /// This is the key to boolean constraint propagation with watched literals.
    /// This method is called to check if there exists a literal that can be
    /// the `wlpos`th watched literal.
    ///
    /// If the current literal is still falsifiable, then the method does nothing
    /// and returns true. However, in the case where a new watched literal needs
    /// to be found, it will iterate over the remaining possible candidates.
    /// In the event where a new WL is found, then this method swaps the position
    /// of the old WL with that of the new and returns true. In the event where
    /// no new WL can be found, the method returns false as a means to tell the
    /// caller that some propagation must occur.
    fn falsifiable_watched_literal(&mut self, cp: &mut dyn CpModel, wlpos: usize) -> bool {
        if cp.is_true(self.literals[wlpos]) {
            let other = self
                .literals
                .iter()
                .copied()
                .enumerate()
                .skip(2)
                .find(|(_, lit)| cp.contains(*lit, 0));

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
mod tests_isand {
    use crate::prelude::*;

    #[test]
    fn empty_clause_is_always_true() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = vec![];

        cp.install(&mut IsAnd::new(b, x));
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_true(b));
    }
    #[test]
    fn unit_clause_means_b_and_single_literal_are_equal() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let c = cp.new_bool_var();
        let x = vec![c];

        cp.install(&mut IsAnd::new(b, x));
        assert!(cp.fixpoint().is_ok());
        assert!(!cp.is_fixed(b));
        assert!(!cp.is_fixed(c));

        cp.save_state();
        cp.fix_bool(c, true).ok();
        cp.fixpoint().ok();
        assert!(cp.is_true(b));
        assert!(cp.is_true(b));

        cp.restore_state();
        cp.save_state();
        cp.fix_bool(c, false).ok();
        cp.fixpoint().ok();
        assert!(cp.is_false(b));
        assert!(cp.is_false(b));

        cp.restore_state();
        cp.save_state();
        cp.fix_bool(b, true).ok();
        cp.fixpoint().ok();
        assert!(cp.is_true(b));
        assert!(cp.is_true(b));

        cp.restore_state();
        cp.save_state();
        cp.fix_bool(b, false).ok();
        cp.fixpoint().ok();
        assert!(cp.is_false(b));
        assert!(cp.is_false(b));
    }

    #[test]
    fn focing_all_literals_to_true_must_satisfy_b() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = vec![
            cp.new_bool_var(),
            cp.new_bool_var(),
            cp.new_bool_var(),
            cp.new_bool_var(),
        ];

        cp.install(&mut IsAnd::new(b, x.clone()));
        cp.fixpoint().ok();

        for l in x {
            cp.fix_bool(l, true).ok();
            cp.fixpoint().ok();
        }
        assert!(cp.is_true(b));
    }

    #[test]
    fn focing_some_watched_literals_to_false_must_falsify_b() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = vec![
            cp.new_bool_var(),
            cp.new_bool_var(),
            cp.new_bool_var(),
            cp.new_bool_var(),
        ];

        cp.install(&mut IsAnd::new(b, x.clone()));
        cp.fixpoint().ok();

        cp.save_state();
        cp.fix_bool(x[0], false).ok();
        cp.fixpoint().ok();
        assert!(cp.is_false(b));

        cp.restore_state();
        cp.save_state();
        cp.fix_bool(x[1], false).ok();
        cp.fixpoint().ok();
        assert!(cp.is_false(b));
    }

    #[test]
    fn focing_b_to_true_must_turn_all_literals_true() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = vec![
            cp.new_bool_var(),
            cp.new_bool_var(),
            cp.new_bool_var(),
            cp.new_bool_var(),
        ];

        cp.install(&mut IsAnd::new(b, x.clone()));
        cp.fixpoint().ok();

        cp.fix_bool(b, true).ok();
        cp.fixpoint().ok();
        for l in x {
            assert!(cp.is_true(l));
        }
    }

    #[test]
    fn focing_b_to_false_eventually_turns_a_literal_off() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let x = vec![
            cp.new_bool_var(),
            cp.new_bool_var(),
            cp.new_bool_var(),
            cp.new_bool_var(),
        ];

        cp.install(&mut IsAnd::new(b, x.clone()));
        cp.fixpoint().ok();

        cp.fix_bool(b, false).ok();
        cp.fixpoint().ok();

        for l in x.iter().copied().take(3) {
            assert!(!cp.is_fixed(l));
            cp.fix_bool(l, true).ok();
            cp.fixpoint().ok();
        }

        assert!(cp.is_false(x[3]));
    }

    #[test]
    fn it_works_fine_with_duplicates() {
        let mut cp = DefaultCpModel::default();
        let b = cp.new_bool_var();
        let c = cp.new_bool_var();
        let x = vec![c, c];

        cp.install(&mut IsAnd::new(b, x));
        assert!(cp.fixpoint().is_ok());

        cp.save_state();
        assert!(cp.fix_bool(c, false).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_false(b));

        cp.restore_state();
        cp.save_state();
        assert!(cp.fix_bool(c, true).is_ok());
        assert!(cp.fixpoint().is_ok());
        assert!(cp.is_true(b));
    }
}
