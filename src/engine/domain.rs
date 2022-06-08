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

//! This module provides the definition and implementation of the variables,
//! DomainStore and DomainBroker

use crate::{ReversibleInt, ReversibleSparseSet, StateManager, TrailedStateManager};

/// This is the kind of error that gets raised whenever a propagator fails
#[derive(Debug, Clone, Copy, thiserror::Error, PartialEq, Eq, Hash)]
#[error("inconsistency")]
pub struct Inconsistency;

/// The result of a propagation operation. (Note: all propagation opertations
/// can fail, in which case they raise an Inconsistency error)
pub type CPResult<T> = Result<T, Inconsistency>;

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
    /// Forces the value of this boolean variable. It returns an Inconsistency
    /// error when fixing the value of the target variable is impossible.
    /// (Caution: this method should be used for booleans [binary 0,1] variables
    /// only. No check is foreseen to enfore this requirement however).
    fn fix_bool(&mut self, var: Variable, value: bool) -> CPResult<()> {
        self.fix(var, if value { 1 } else { 0 })
    }
}

/// An event that tells what happened to the domain of a variable
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

/// This is the type of domain store implementation you will likely want to use
/// in your solver. Currently, this is the only available implementation of a DS
/// but it *might* possibly change in the future.
pub type DefaultDomainStore = DomainStoreImpl<TrailedStateManager>;

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
        let id = self.state.increment(self.n_vars) as usize - 1;
        let n = (max - min + 1) as usize;
        let domain = self.state.manage_sparse_set(n, min);

        let variable = Variable(id);
        if self.domains.len() <= id {
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
            let min_changed = self.state.sparse_set_get_min(dom) != Some(value);
            let max_changed = self.state.sparse_set_get_max(dom) != Some(value);
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

            let domain_changed = self.state.sparse_set_remove(dom, value);
            let size = self.state.sparse_set_size(dom);
            let is_fixed = size == 1;
            let is_empty = size == 0;

            self.events[var.0].min_changed |= min_changed;
            self.events[var.0].max_changed |= max_changed;
            self.events[var.0].is_fixed |= is_fixed;
            self.events[var.0].is_empty |= is_empty;
            self.events[var.0].domain_changed |= domain_changed;

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
        let max_changed = self.state.sparse_set_get_max(dom) > Some(value);

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
            .filter(|e| e.is_empty | e.is_fixed | e.max_changed | e.min_changed | e.domain_changed)
            .for_each(f);
    }
}

// #############################################################################
// ### UNIT TESTS ##############################################################
// #############################################################################
#[cfg(test)]
mod test_domainstoreimpl_domainbroker {
    use super::*;

    #[test]
    fn save_and_restore_state_should_work_together() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_bool_var();

        assert!(!ds.is_fixed(x));
        assert!(!ds.is_fixed(y));
        assert_eq!(ds.size(x), 6);
        assert_eq!(ds.size(y), 2);
        ds.save_state();

        assert_eq!(ds.fix(x, 9), Ok(()));
        assert_eq!(ds.fix_bool(y, false), Ok(()));

        assert!(ds.is_fixed(x));
        assert!(ds.is_fixed(y));
        assert_eq!(ds.size(x), 1);
        assert_eq!(ds.size(y), 1);

        assert_eq!(ds.min(x), Some(9));
        assert!(ds.is_false(y));

        ds.restore_state();
        assert!(!ds.is_fixed(x));
        assert!(!ds.is_fixed(y));
        assert_eq!(ds.size(x), 6);
        assert_eq!(ds.size(y), 2);
    }

    #[test]
    fn foreach_event_skips_empty_events() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_bool_var();

        let mut count = 0;
        ds.for_each_event(|_e| {
            count += 1;
        });
        assert_eq!(0, count);

        // when change has no impact
        assert_eq!(Ok(()), ds.remove(x, 4)); // has absolutely no impact
        assert_eq!(Ok(()), ds.remove(y, 4)); // has absolutely no impact
        ds.for_each_event(|_e| {
            count += 1;
        });
        assert_eq!(0, count);
    }

    #[test]
    fn foreach_event_goes_over_events() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_bool_var();

        // when change has impact
        assert_eq!(Ok(()), ds.remove(x, 7));
        assert_eq!(Ok(()), ds.remove(y, 1));

        let mut count = 0;
        ds.for_each_event(|e| {
            count += 1;
            if e.variable == x {
                assert!(!e.is_empty);
                assert!(!e.is_fixed);
                assert!(!e.min_changed);
                assert!(!e.max_changed);
                assert!(e.domain_changed);
            }
            if e.variable == y {
                assert!(!e.is_empty);
                assert!(e.is_fixed);
                assert!(!e.min_changed);
                assert!(e.max_changed);
                assert!(e.domain_changed);
            }
        });
        assert_eq!(2, count);
    }

    #[test]
    fn clear_events_resets_all_events() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_bool_var();

        // when change has no impact
        assert_eq!(Ok(()), ds.remove(x, 7));
        assert_eq!(Ok(()), ds.remove(y, 1));

        let mut count = 0;
        ds.for_each_event(|_| {
            count += 1;
        });
        assert_eq!(2, count);

        ds.clear_events();
        count = 0;
        ds.for_each_event(|_| {
            count += 1;
        });
        assert_eq!(0, count);
    }
}

#[cfg(test)]
mod test_domainstoreimpl_domainstore {
    use super::*;

    #[test]
    fn min_yields_the_minimum_of_domain() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Some(5), ds.min(x));
        assert_eq!(Some(0), ds.min(y));
        assert_eq!(Some(0), ds.min(z));
    }
    #[test]
    fn min_yields_the_minimum_of_domain_after_update() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove_below(x, 7));
        assert_eq!(Ok(()), ds.remove_below(y, 3));
        assert_eq!(Ok(()), ds.remove_below(z, 1));

        assert_eq!(Some(7), ds.min(x));
        assert_eq!(Some(3), ds.min(y));
        assert_eq!(Some(1), ds.min(z));
    }
    #[test]
    fn min_yields_none_when_domain_is_empty() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Err(Inconsistency), ds.remove_below(x, 20));
        assert_eq!(Err(Inconsistency), ds.remove_below(y, 20));
        assert_eq!(Err(Inconsistency), ds.remove_below(z, 20));

        assert_eq!(None, ds.min(x));
        assert_eq!(None, ds.min(y));
        assert_eq!(None, ds.min(z));
    }

    #[test]
    fn max_yields_the_maximum_of_domain() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Some(10), ds.max(x));
        assert_eq!(Some(5), ds.max(y));
        assert_eq!(Some(1), ds.max(z));
    }
    #[test]
    fn max_yields_the_maximum_of_domain_after_update() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove_above(x, 7));
        assert_eq!(Ok(()), ds.remove_above(y, 3));
        assert_eq!(Ok(()), ds.remove_above(z, 0));

        assert_eq!(Some(7), ds.max(x));
        assert_eq!(Some(3), ds.max(y));
        assert_eq!(Some(0), ds.max(z));
    }
    #[test]
    fn max_yields_none_when_domain_is_empty() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Err(Inconsistency), ds.remove_above(x, -1));
        assert_eq!(Err(Inconsistency), ds.remove_above(y, -1));
        assert_eq!(Err(Inconsistency), ds.remove_above(z, -1));

        assert_eq!(None, ds.max(x));
        assert_eq!(None, ds.max(y));
        assert_eq!(None, ds.max(z));
    }

    #[test]
    fn size_yields_the_domain_size() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(6, ds.size(x));
        assert_eq!(6, ds.size(y));
        assert_eq!(2, ds.size(z));
    }
    #[test]
    fn size_yields_the_domain_size_with_hole() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove(x, 7));
        assert_eq!(Ok(()), ds.remove(y, 3));
        assert_eq!(Ok(()), ds.remove(z, 1));

        assert_eq!(5, ds.size(x));
        assert_eq!(5, ds.size(y));
        assert_eq!(1, ds.size(z));
    }
    #[test]
    fn size_yields_the_domain_size_change_lb() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove_below(x, 7));
        assert_eq!(Ok(()), ds.remove_below(y, 3));
        assert_eq!(Ok(()), ds.remove_below(z, 1));

        assert_eq!(4, ds.size(x));
        assert_eq!(3, ds.size(y));
        assert_eq!(1, ds.size(z));
    }
    #[test]
    fn size_yields_the_domain_size_change_ub() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove_above(x, 7));
        assert_eq!(Ok(()), ds.remove_above(y, 3));
        assert_eq!(Ok(()), ds.remove_above(z, 0));

        assert_eq!(3, ds.size(x));
        assert_eq!(4, ds.size(y));
        assert_eq!(1, ds.size(z));
    }

    #[test]
    fn contains_returns_false_for_value_less_than_lb() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert!(!ds.contains(x, -5));
        assert!(!ds.contains(y, -5));
        assert!(!ds.contains(z, -5));
    }
    #[test]
    fn contains_returns_true_for_lb() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert!(ds.contains(x, 5));
        assert!(ds.contains(y, 0));
        assert!(ds.contains(z, 0));
    }
    #[test]
    fn contains_returns_false_for_value_gt_than_ub() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert!(!ds.contains(x, 45));
        assert!(!ds.contains(y, 45));
        assert!(!ds.contains(z, 45));
    }
    #[test]
    fn contains_returns_true_for_ub() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert!(ds.contains(x, 10));
        assert!(ds.contains(y, 5));
        assert!(ds.contains(z, 1));
    }
    #[test]
    fn contains_returns_false_for_hole() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove(x, 7));
        assert_eq!(Ok(()), ds.remove(y, 3));
        assert_eq!(Ok(()), ds.remove(z, 0));

        assert!(!ds.contains(x, 7));
        assert!(!ds.contains(y, 3));
        assert!(!ds.contains(z, 0));
    }
    #[test]
    fn contains_returns_true_if_in_set() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove(x, 7));
        assert_eq!(Ok(()), ds.remove(y, 3));
        assert_eq!(Ok(()), ds.remove(z, 0));

        assert!(ds.contains(x, 6));
        assert!(ds.contains(y, 2));
        assert!(ds.contains(z, 1));
    }

    #[test]
    fn fix_fails_when_lower_than_lb() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Err(Inconsistency), ds.fix(x, -10));
        assert_eq!(Err(Inconsistency), ds.fix(y, -10));
        assert_eq!(Err(Inconsistency), ds.fix(z, -10));
    }
    #[test]
    fn fix_fails_when_higher_than_ub() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Err(Inconsistency), ds.fix(x, 20));
        assert_eq!(Err(Inconsistency), ds.fix(y, 20));
        assert_eq!(Err(Inconsistency), ds.fix(z, 20));
    }
    #[test]
    fn fix_fails_when_hole() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove(x, 7));
        assert_eq!(Ok(()), ds.remove(y, 3));
        assert_eq!(Ok(()), ds.remove(z, 0));

        assert_eq!(Err(Inconsistency), ds.fix(x, 7));
        assert_eq!(Err(Inconsistency), ds.fix(y, 3));
        assert_eq!(Err(Inconsistency), ds.fix(z, 0));
    }
    #[test]
    fn fix_succeeds_when_in_domain() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.fix(x, 7));
        assert_eq!(Ok(()), ds.fix(y, 3));
        assert_eq!(Ok(()), ds.fix(z, 0));
    }
    #[test]
    fn fix_sets_events() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.fix(x, 7));
        assert_eq!(Ok(()), ds.fix(y, 3));
        assert_eq!(Ok(()), ds.fix(z, 0));

        assert_eq!(
            ds.events[x.0],
            DomainEvent {
                variable: x,
                is_fixed: true,
                is_empty: false,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[y.0],
            DomainEvent {
                variable: y,
                is_fixed: true,
                is_empty: false,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[z.0],
            DomainEvent {
                variable: z,
                is_fixed: true,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
    }

    #[test]
    fn remove_has_no_effect_when_out_of_domain() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove(x, -10));
        assert_eq!(Ok(()), ds.remove(y, -10));
        assert_eq!(Ok(()), ds.remove(z, -10));

        assert_eq!(
            ds.events[x.0],
            DomainEvent {
                variable: x,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[y.0],
            DomainEvent {
                variable: y,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[z.0],
            DomainEvent {
                variable: z,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
    }

    #[test]
    fn remove_fails_when_it_makes_domain_empty() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove_below(x, 7));
        assert_eq!(Ok(()), ds.remove_below(y, 3));
        assert_eq!(Ok(()), ds.remove_below(z, 0));

        assert_eq!(Ok(()), ds.remove_above(x, 7));
        assert_eq!(Ok(()), ds.remove_above(y, 3));
        assert_eq!(Ok(()), ds.remove_above(z, 0));

        assert_eq!(Err(Inconsistency), ds.remove(x, 7));
        assert_eq!(Err(Inconsistency), ds.remove(y, 3));
        assert_eq!(Err(Inconsistency), ds.remove(z, 0));

        assert_eq!(
            ds.events[x.0],
            DomainEvent {
                variable: x,
                is_fixed: true,
                is_empty: true,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[y.0],
            DomainEvent {
                variable: y,
                is_fixed: true,
                is_empty: true,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[z.0],
            DomainEvent {
                variable: z,
                is_fixed: true,
                is_empty: true,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
    }
    #[test]
    fn remove_punches_a_hole_when_in_the_middle() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove(x, 7));
        assert_eq!(Ok(()), ds.remove(y, 3));
        assert_eq!(Ok(()), ds.remove(z, 0));

        assert_eq!(
            ds.events[x.0],
            DomainEvent {
                variable: x,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[y.0],
            DomainEvent {
                variable: y,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[z.0],
            DomainEvent {
                variable: z,
                is_fixed: true,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
    }

    #[test]
    fn remove_may_adapt_minimum() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove(x, 5));
        assert_eq!(Ok(()), ds.remove(y, 0));
        assert_eq!(Ok(()), ds.remove(z, 0));

        assert_eq!(Some(6), ds.min(x));
        assert_eq!(Some(1), ds.min(y));
        assert_eq!(Some(1), ds.min(z));

        assert_eq!(Some(10), ds.max(x));
        assert_eq!(Some(5), ds.max(y));
        assert_eq!(Some(1), ds.max(z));

        assert_eq!(
            ds.events[x.0],
            DomainEvent {
                variable: x,
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[y.0],
            DomainEvent {
                variable: y,
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[z.0],
            DomainEvent {
                variable: z,
                is_fixed: true,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
    }

    #[test]
    fn remove_may_adapt_maximum() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove(x, 10));
        assert_eq!(Ok(()), ds.remove(y, 5));
        assert_eq!(Ok(()), ds.remove(z, 1));

        assert_eq!(Some(5), ds.min(x));
        assert_eq!(Some(0), ds.min(y));
        assert_eq!(Some(0), ds.min(z));

        assert_eq!(Some(9), ds.max(x));
        assert_eq!(Some(4), ds.max(y));
        assert_eq!(Some(0), ds.max(z));

        assert_eq!(
            ds.events[x.0],
            DomainEvent {
                variable: x,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[y.0],
            DomainEvent {
                variable: y,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[z.0],
            DomainEvent {
                variable: z,
                is_fixed: true,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
    }

    #[test]
    fn remove_above_has_no_effect_when_out_of_domain() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove_above(x, 20));
        assert_eq!(Ok(()), ds.remove_above(y, 20));
        assert_eq!(Ok(()), ds.remove_above(z, 20));

        assert_eq!(
            ds.events[x.0],
            DomainEvent {
                variable: x,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[y.0],
            DomainEvent {
                variable: y,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[z.0],
            DomainEvent {
                variable: z,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
    }

    #[test]
    fn remove_above_fails_when_it_makes_domain_empty() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Err(Inconsistency), ds.remove_above(x, -10));
        assert_eq!(Err(Inconsistency), ds.remove_above(y, -10));
        assert_eq!(Err(Inconsistency), ds.remove_above(z, -10));

        assert_eq!(
            ds.events[x.0],
            DomainEvent {
                variable: x,
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[y.0],
            DomainEvent {
                variable: y,
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[z.0],
            DomainEvent {
                variable: z,
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
    }

    #[test]
    fn remove_above_may_adapt_maximum() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove_above(x, 7));
        assert_eq!(Ok(()), ds.remove_above(y, 3));
        assert_eq!(Ok(()), ds.remove_above(z, 0));

        assert_eq!(Some(5), ds.min(x));
        assert_eq!(Some(0), ds.min(y));
        assert_eq!(Some(0), ds.min(z));

        assert_eq!(Some(7), ds.max(x));
        assert_eq!(Some(3), ds.max(y));
        assert_eq!(Some(0), ds.max(z));

        assert_eq!(
            ds.events[x.0],
            DomainEvent {
                variable: x,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[y.0],
            DomainEvent {
                variable: y,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[z.0],
            DomainEvent {
                variable: z,
                is_fixed: true,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
    }

    #[test]
    fn remove_below_has_no_effect_when_out_of_domain() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove_below(x, -20));
        assert_eq!(Ok(()), ds.remove_below(y, -20));
        assert_eq!(Ok(()), ds.remove_below(z, -20));

        assert_eq!(
            ds.events[x.0],
            DomainEvent {
                variable: x,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[y.0],
            DomainEvent {
                variable: y,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[z.0],
            DomainEvent {
                variable: z,
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
    }

    #[test]
    fn remove_below_fails_when_it_makes_domain_empty() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Err(Inconsistency), ds.remove_below(x, 20));
        assert_eq!(Err(Inconsistency), ds.remove_below(y, 20));
        assert_eq!(Err(Inconsistency), ds.remove_below(z, 20));

        assert_eq!(
            ds.events[x.0],
            DomainEvent {
                variable: x,
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[y.0],
            DomainEvent {
                variable: y,
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[z.0],
            DomainEvent {
                variable: z,
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
    }

    #[test]
    fn remove_below_may_adapt_minimum() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove_below(x, 7));
        assert_eq!(Ok(()), ds.remove_below(y, 3));
        assert_eq!(Ok(()), ds.remove_below(z, 1));

        assert_eq!(Some(7), ds.min(x));
        assert_eq!(Some(3), ds.min(y));
        assert_eq!(Some(1), ds.min(z));

        assert_eq!(Some(10), ds.max(x));
        assert_eq!(Some(5), ds.max(y));
        assert_eq!(Some(1), ds.max(z));

        assert_eq!(
            ds.events[x.0],
            DomainEvent {
                variable: x,
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[y.0],
            DomainEvent {
                variable: y,
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[z.0],
            DomainEvent {
                variable: z,
                is_fixed: true,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
    }

    #[test]
    fn is_fixed_only_when_one_value_left() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert!(!ds.is_fixed(x));
        assert!(!ds.is_fixed(y));
        assert!(!ds.is_fixed(z));
        ds.save_state();

        assert_eq!(Ok(()), ds.fix(x, 7));
        assert_eq!(Ok(()), ds.fix(y, 3));
        assert_eq!(Ok(()), ds.fix(z, 0));
        assert!(ds.is_fixed(x));
        assert!(ds.is_fixed(y));
        assert!(ds.is_fixed(z));
        ds.restore_state();

        assert!(!ds.is_fixed(x));
        assert!(!ds.is_fixed(y));
        assert!(!ds.is_fixed(z));
    }
    #[test]
    fn is_true_iff_fixed_and_true() {
        let mut ds = DefaultDomainStore::default();
        let z = ds.new_bool_var();

        assert!(!ds.is_true(z));
        ds.save_state();

        assert_eq!(Ok(()), ds.fix(z, 0));
        assert!(!ds.is_true(z));
        ds.restore_state();

        assert!(!ds.is_true(z));
        assert_eq!(Ok(()), ds.fix(z, 1));
        assert!(ds.is_true(z));
    }
    #[test]
    fn is_false_iff_fixed_and_false() {
        let mut ds = DefaultDomainStore::default();
        let z = ds.new_bool_var();

        assert!(!ds.is_false(z));
        ds.save_state();

        assert_eq!(Ok(()), ds.fix(z, 0));
        assert!(ds.is_false(z));
        ds.restore_state();

        assert!(!ds.is_false(z));
        assert_eq!(Ok(()), ds.fix(z, 1));
        assert!(!ds.is_false(z));
    }
}
