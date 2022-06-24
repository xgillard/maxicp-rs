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

//! This module provides the implementation of the "sum" constraint.

use crate::prelude::*;

/// This constraint enforces that the sum of all variables be zero.
/// In other words, sum(xs) == 0
#[derive(Debug, Clone)]
pub struct Sum {
    /// The sum of all these terms must be zero
    terms: Vec<Variable>,
}

impl Sum {
    /// Creates a new instance of the constraint
    pub fn new(terms: Vec<Variable>) -> Self {
        Self { terms }
    }
}

impl ModelingConstruct for Sum {
    fn install(&mut self, cp: &mut CpModel) {
        let propag = Box::new(SumPropagator::new(cp, &self.terms));
        let propag = cp.post(propag);

        cp.schedule(propag);
        for x in self.terms.iter().copied() {
            cp.propagate_on(propag, DomainCondition::MinimumChanged(x));
            cp.propagate_on(propag, DomainCondition::MaximumChanged(x));
        }
    }
}

/// A fat var is nothing but a variable with some additional bookeeping of
/// the minimum and maximum in the domain of that var. The whole point of this
/// structure is to make it easy to swap terms in the propagator so as to
/// facilitate the tracking of the fixed/unfixed vars while keeping the min max
/// queries extremely efficient.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
struct FatVar {
    var: Variable,
    min: isize,
    max: isize,
}

/// This is the propagator that gets used to propagate a sum constraint.
///
/// The propagator works as follows: at any point of time, the propagator
/// tracks the terms that are fixed and those that are not. This gives it the
/// ability to avoid iterating over and over on these terms that have been
/// fixed.  Based on this set of fixed/not fixed terms, the propagator keeps
/// track of the partial sum of the fixed terms values (again to avoid to
/// systematically recompute that bit).
///
/// The propagation is thus the following: a lower bound and an upper bound on
/// the total sum are computed based on the terms that have not been fixed.
/// Then, the lower and upper bounds are enforced on all remaining terms.
/// These are respecively given for any term `x` by:
/// * *LOWER BOUND* = -total_max + xmax
/// * *UPPER BOUND* = -total_min + xmin
///
/// # Note
/// For the sake of efficiency, the solver also maintains the minimum and
/// maximum of each variable.
struct SumPropagator {
    /// The sum of all these terms must be zero.
    ///
    /// # Note
    /// This structure maintains the invariant that the first `n_fixed` elements
    /// of the list are fixed and the others remain open.
    terms: Vec<FatVar>,
    /// This integer delimitates the region in `terms` that comprises only fixed
    /// variables
    n_fixed: ReversibleInt,
    /// This integer simply keeps track of the partial sum of the fixed vars
    partial: ReversibleInt,
}

impl SumPropagator {
    /// Creates a propagator for the given sum constraint
    fn new(cp: &mut CpModel, terms: &[Variable]) -> Self {
        let terms = terms
            .iter()
            .copied()
            .map(|x| FatVar {
                var: x,
                min: 0,
                max: 0,
            })
            .collect();

        let n_fixed = cp.state_manager_mut().manage_int(0);
        let partial = cp.state_manager_mut().manage_int(0);
        Self {
            terms,
            n_fixed,
            partial,
        }
    }
}
impl Propagator for SumPropagator {
    fn propagate(&mut self, cp: &mut CpModel) -> CPResult<()> {
        // start bookkeeping
        let n = self.terms.len();
        let mut fixed = cp.state_manager().get_int(self.n_fixed) as usize;
        let mut partial = cp.state_manager().get_int(self.partial);
        let mut total_min = partial;
        let mut total_max = partial;

        for i in fixed..n {
            let mut x = self.terms[i];
            x.min = cp.min(x.var).unwrap();
            x.max = cp.max(x.var).unwrap();

            self.terms[i] = x;
            total_min += x.min;
            total_max += x.max;

            if cp.is_fixed(x.var) {
                self.terms.swap(fixed, i);
                partial += x.min;
                fixed += 1;
            }
        }
        // detect impossible
        if total_min > 0 || total_max < 0 {
            return Err(Inconsistency);
        }
        // prune domains
        for x in self.terms.iter().skip(fixed).copied() {
            cp.remove_above(x.var, -total_min + x.min)?;
            cp.remove_below(x.var, -total_max + x.max)?;
        }
        // finalize bookkeeping
        cp.state_manager_mut().set_int(self.n_fixed, fixed as isize);
        cp.state_manager_mut().set_int(self.partial, partial);

        Ok(())
    }
}