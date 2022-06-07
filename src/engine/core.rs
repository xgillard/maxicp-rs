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

//! This module provides the definition and implementation of the solver's
//! core abstractions (IntVar, BoolVar, Constraints, ...)

use crate::{ReversibleInt, ReversibleSparseSet, StateManager};

/// This is the kind of error that gets raised whenever a propagator fails
#[derive(Debug, Clone, Copy, thiserror::Error, PartialEq, Eq, Hash)]
#[error("inconsistency")]
pub struct Inconsistency;

/// The result of a propagation operation. (Note: all propagation opertations
/// can fail, in which case they raise an Inconsistency error)
pub type CPResult<T> = Result<T, Inconsistency>;

/// An identifier to a constraint. A constraint in itself is really just
/// an identifier in this implementation. The bulk of the work is done by
/// the solver.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Constraint(usize);

/// The propagator is the portion of the code where the magic actually happens.
/// A propagator is called by the solver during the fixpoint computation. It
/// enforces a certain level of consistency on the domain of the variables it
/// works on.
pub trait Propagator {
    /// Actually runs the custom propagation algorithm
    fn propagate(&mut self, domain_store: &mut dyn DomainStore) -> CPResult<()>;
}

/// An integer variable that can be used in a CP model
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Variable(usize);

/// A domain store is the entity that gives a hook to propagators for modifying
/// the variables domains. (Note however that no propagator can directly access
/// the events associated with a given variable, nor decide to save or restore
/// the state of these domaims to a previous value. These are the
/// responsibilities devoted to a DomainBroker -- which is typically implemented
/// by the same structure as DomainStore; but it helps to split responsibilities).
pub trait DomainStore {
    /// Creates a new integer variable covering the min..=max range of values
    fn new_int_var(&mut self, min: isize, max: isize) -> Variable;
    /// Returns the minimum value of the doman of this variable (if it exists)
    fn min(&self, var: Variable) -> Option<isize>;
    /// Returns the maximum value of the doman of this variable (if it exists)
    fn max(&self, var: Variable) -> Option<isize>;
    /// Returns the size of the domain of this variable
    fn size(&self, var: Variable) -> usize;
    /// Returns true iff the domain of the target `var` contains the specified `value`
    fn contains(&self, var: Variable, value: isize) -> bool;
    /// Returns true iff the value of the target variable is fixed/imposed
    fn is_fixed(&self, var: Variable) -> bool {
        self.size(var) == 1
    }
    /// Forces the value of this variable. It returns an Inconsistency error
    /// when fixing the value of the target variable is impossible
    fn fix(&mut self, var: Variable, value: isize) -> CPResult<()>;
    /// Removes the specified value from the domain of the target variable.
    /// An Inconsistency error is returned when the domain of the variable
    /// becomes empty because of this removal
    fn remove(&mut self, var: Variable, value: isize) -> CPResult<()>;
    /// Removes all value less than (<) the specified value from the domain
    /// of the target variable. An Inconsistency error is returned when the
    /// domain of the variable becomes empty because of this removal
    fn remove_below(&mut self, var: Variable, value: isize) -> CPResult<()>;
    /// Removes all value greater than (>) the specified value from the domain
    /// of the target variable. An Inconsistency error is returned when the
    /// domain of the variable becomes empty because of this removal
    fn remove_above(&mut self, var: Variable, value: isize) -> CPResult<()>;

    /// Creates a new binary 0,1 variable
    fn new_bool_var(&mut self) -> Variable {
        self.new_int_var(0, 1)
    }
    /// Tests if the variable is fixed to true (Caution: this should only be
    /// applied to binary 0,1 variables. No check is foreseen to verify you
    /// comply with that requirement)
    fn is_true(&self, var: Variable) -> bool {
        self.min(var) == Some(1)
    }
    /// Tests if the variable is fixed to false (Caution: this should only be
    /// applied to binary 0,1 variables. No check is foreseen to verify you
    /// comply with that requirement)
    fn is_false(&self, var: Variable) -> bool {
        self.max(var) == Some(0)
    }
}

/// An event that tells what happened to the domain of a variable
#[derive(Debug, Clone, Copy)]
pub struct DomainEvent {
    /// This is the variable impacted by a possible change in its domain
    pub variable: Variable,
    /// This flag is set when the domain of the variable has become fixed
    /// (That is, it only has one single value left in its domain)
    pub is_fixed: bool,
    /// This flag is set when the domain of a variable has become empty
    /// (this should somehow have triggered an Inconsistency error)
    pub is_empty: bool,
    /// This flag is set when the domain's minimum has changed
    pub min_changed: bool,
    /// This flag is set when the domain's maximum has changed
    pub max_changed: bool,
    /// This flag is set when a change has occured in the domain of the variable
    /// (this is the weakest of the requirements to set a flag)
    pub domain_changed: bool,
}

/// The domain borker is the facet of the domain store which is in charge of
/// tracking all changes occurring in the domain of the variables. A domain
/// broker is the object which is used by the solver to schedule the propagation
/// of the various propagators and listeners.
pub trait DomainBroker {
    /// saves the current state of all variables
    fn save_state(&mut self);
    /// restores the previous state of all variables
    fn restore_state(&mut self);
    /// forgets all events that have happened on a variable
    fn clear_events(&mut self);
    /// goes over all the events that have occurred on the variables
    fn for_each_event<F: FnMut(DomainEvent)>(&self, f: F);
}

/// This is a simple implementation of a domain store. It implements both the
/// DomainStore and the DomainBroker traits, which means it really is an entity
/// that encompasses the complete lifecycle of a variable (but has nothing to
/// do with the higher level constructs that *use* the events applied to these
/// variables)
pub struct DomainStoreImpl<T: StateManager> {
    /// The state manager in charge of saving/restoring the domains states
    state: T,
    /// How many variables are there right now ?
    n_vars: ReversibleInt,
    /// The domains of all variables
    domains: Vec<ReversibleSparseSet>,
    /// The events that have been applied to
    events: Vec<DomainEvent>,
}
impl<T: StateManager> DomainStoreImpl<T> {
    /// Creates a new instance of the domain store based on the given state
    /// manager
    pub fn new(mut state: T) -> Self {
        let n_vars = state.manage_int(0);
        Self {
            state,
            n_vars,
            domains: vec![],
            events: vec![],
        }
    }
}

impl<T: StateManager> From<T> for DomainStoreImpl<T> {
    fn from(state: T) -> Self {
        Self::new(state)
    }
}
impl<T: StateManager + Default> Default for DomainStoreImpl<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T: StateManager> DomainStore for DomainStoreImpl<T> {
    fn new_int_var(&mut self, min: isize, max: isize) -> Variable {
        let id = self.state.increment(self.n_vars) as usize;
        let n = (max - min + 1) as usize;
        let domain = self.state.manage_sparse_set(n, min);

        let variable = Variable(id);
        if self.domains.len() < id {
            // its a fresh variable
            self.domains.push(domain);
            self.events.push(DomainEvent {
                variable,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            });
        } else {
            // let us recycle the old data
            self.domains[id] = domain;
            self.events[id] = DomainEvent {
                variable,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            };
        }
        variable
    }

    fn min(&self, var: Variable) -> Option<isize> {
        self.state.sparse_set_get_min(self.domains[var.0])
    }

    fn max(&self, var: Variable) -> Option<isize> {
        self.state.sparse_set_get_max(self.domains[var.0])
    }

    fn size(&self, var: Variable) -> usize {
        self.state.sparse_set_size(self.domains[var.0])
    }

    fn contains(&self, var: Variable, value: isize) -> bool {
        self.state.sparse_set_contains(self.domains[var.0], value)
    }

    fn fix(&mut self, var: Variable, value: isize) -> CPResult<()> {
        let dom = self.domains[var.0];

        if self.contains(var, value) && self.is_fixed(var) {
            // if there is nothing to do, then we're done
            CPResult::Ok(())
        } else {
            let min_changed = self.state.sparse_set_get_min(dom) == Some(value);
            let max_changed = self.state.sparse_set_get_max(dom) == Some(value);
            self.state.sparse_set_remove_all_but(dom, value);
            if self.state.sparse_set_is_empty(dom) {
                self.events[var.0].min_changed |= min_changed;
                self.events[var.0].max_changed |= max_changed;
                self.events[var.0].domain_changed = true;
                self.events[var.0].is_empty = true;
                CPResult::Err(Inconsistency)
            } else {
                self.events[var.0].min_changed |= min_changed;
                self.events[var.0].max_changed |= max_changed;
                self.events[var.0].domain_changed = true;
                self.events[var.0].is_fixed = true;
                CPResult::Ok(())
            }
        }
    }

    fn remove(&mut self, var: Variable, value: isize) -> CPResult<()> {
        if !self.contains(var, value) {
            // there is nothing to do
            CPResult::Ok(())
        } else {
            let dom = self.domains[var.0];
            let min_changed = self.state.sparse_set_get_min(dom) == Some(value);
            let max_changed = self.state.sparse_set_get_max(dom) == Some(value);

            self.state.sparse_set_remove(dom, value);
            let size = self.state.sparse_set_size(dom);
            let is_fixed = size == 1;
            let is_empty = size == 0;

            self.events[var.0].min_changed |= min_changed;
            self.events[var.0].max_changed |= max_changed;
            self.events[var.0].is_fixed |= is_fixed;
            self.events[var.0].is_empty |= is_empty;
            self.events[var.0].domain_changed |= true;

            if is_empty {
                CPResult::Err(Inconsistency)
            } else {
                CPResult::Ok(())
            }
        }
    }

    fn remove_below(&mut self, var: Variable, value: isize) -> CPResult<()> {
        let dom = self.domains[var.0];
        let min_changed = self.state.sparse_set_get_min(dom) < Some(value);

        if min_changed {
            self.state.sparse_set_remove_below(dom, value);
            let size = self.state.sparse_set_size(dom);

            match size {
                0 => {
                    self.events[var.0].is_empty = true;
                    CPResult::Err(Inconsistency)
                }
                1 => {
                    self.events[var.0].is_fixed = true;
                    self.events[var.0].min_changed = true;
                    self.events[var.0].domain_changed = true;
                    CPResult::Ok(())
                }
                _ => {
                    self.events[var.0].min_changed = true;
                    self.events[var.0].domain_changed = true;
                    CPResult::Ok(())
                }
            }
        } else {
            // Nothing to do
            CPResult::Ok(())
        }
    }

    fn remove_above(&mut self, var: Variable, value: isize) -> CPResult<()> {
        let dom = self.domains[var.0];
        let max_changed = self.state.sparse_set_get_min(dom) > Some(value);

        if max_changed {
            self.state.sparse_set_remove_above(dom, value);
            let size = self.state.sparse_set_size(dom);

            match size {
                0 => {
                    self.events[var.0].is_empty = true;
                    CPResult::Err(Inconsistency)
                }
                1 => {
                    self.events[var.0].is_fixed = true;
                    self.events[var.0].max_changed = true;
                    self.events[var.0].domain_changed = true;
                    CPResult::Ok(())
                }
                _ => {
                    self.events[var.0].max_changed = true;
                    self.events[var.0].domain_changed = true;
                    CPResult::Ok(())
                }
            }
        } else {
            // Nothing to do
            CPResult::Ok(())
        }
    }
}
impl<T: StateManager> DomainBroker for DomainStoreImpl<T> {
    fn save_state(&mut self) {
        self.state.save_state()
    }

    fn restore_state(&mut self) {
        self.state.restore_state()
    }

    fn clear_events(&mut self) {
        for e in self.events.iter_mut() {
            e.is_empty = false;
            e.is_fixed = false;
            e.min_changed = false;
            e.max_changed = false;
            e.domain_changed = false;
        }
    }

    fn for_each_event<F: FnMut(DomainEvent)>(&self, f: F) {
        self.events
            .iter()
            .copied()
            .filter(|e| e.is_empty | e.is_fixed | e.max_changed | e.min_changed)
            .for_each(f);
    }
}
