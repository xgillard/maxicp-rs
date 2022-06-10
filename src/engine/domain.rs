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

use crate::{
    ReversibleInt, ReversibleSparseSet, SaveAndRestore, StateManager, TrailedStateManager,
};

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

    /// Returns a (view) variable corresponding to var * value
    fn mul(&mut self, var: Variable, value: isize) -> Variable;
    /// Returns a (view) variable corresponding to var + value
    fn plus(&mut self, var: Variable, value: isize) -> Variable;
    /// Returns a (view) variable corresponding to var - value
    fn sub(&mut self, var: Variable, value: isize) -> Variable;
    /// Returns a (view) variable corresponding to -var (flips the sign)
    fn neg(&mut self, var: Variable) -> Variable;
    /// Returns a (view) variable corresponding to !var (flips the boolean polarity)
    fn not(&mut self, var: Variable) -> Variable;
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
pub trait DomainBroker: SaveAndRestore {
    /// forgets all events that have happened on a variable
    fn clear_events(&mut self);
    /// goes over all the events that have occurred on the variables
    fn for_each_event<F: FnMut(DomainEvent)>(&self, f: F);
}

/// This is the type of domain store implementation you will likely want to use
/// in your solver. Currently, this is the only available implementation of a DS
/// but it *might* possibly change in the future.
pub type DefaultDomainStore = DomainStoreImpl<TrailedStateManager>;

/// All variables in a CP model are not primitive variables. That is, not all
/// variables have a direct correspondance with a reversible sparse set in the
/// state of the domainstoreimpl. Indeed, some variables are *views* over other
/// variables. This enumeration describes all supported types of primitive
/// variables and views.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum VariableType {
    /// A primitive variable, hence not a view
    Primitive {
        index: usize,
        domain: ReversibleSparseSet,
    },
    /// A view that corresponds to x + offset
    OffsetView { x: Variable, offset: isize },
    /// A view that corresponds to x * coeff
    MultiplicationView { x: Variable, coeff: isize },
    /// A view that flips the sign of the target variable. It corresponds to -x.
    NegativeView { x: Variable },
    /// Flips the boolean polarity of a variable. It corresponds to -x
    FlipView { x: Variable },
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
    /// The information about all variables
    variables: Vec<VariableType>,
    /// How many events slots are there right now ? (How many primitive variables ?)
    n_events: ReversibleInt,
    /// The events attached to all primitive variables
    events: Vec<DomainEvent>,
}
impl<T: StateManager> DomainStoreImpl<T> {
    /// Creates a new instance of the domain store based on the given state
    /// manager
    pub fn new(state: T) -> Self {
        Self::from(state)
    }
    /// Returns a reference to the underlying state manager
    pub fn state_manager(&self) -> &T {
        &self.state
    }
    /// Returns a mutable reference to the underlying state manager
    pub fn state_manager_mut(&mut self) -> &mut T {
        &mut self.state
    }
}

impl<T: StateManager> From<T> for DomainStoreImpl<T> {
    fn from(mut state: T) -> Self {
        let n_vars = state.manage_int(0);
        let n_events = state.manage_int(0);
        Self {
            state,
            n_vars,
            n_events,
            variables: vec![],
            events: vec![],
        }
    }
}
impl<T: StateManager + Default> Default for DomainStoreImpl<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T: StateManager> DomainStore for DomainStoreImpl<T> {
    fn new_int_var(&mut self, min: isize, max: isize) -> Variable {
        let id = (self.state.increment(self.n_vars) - 1) as usize;
        let n = (max - min + 1) as usize;

        let variable = Variable(id);
        let evt_id = (self.state.increment(self.n_events) - 1) as usize;
        let domain = self.state.manage_sparse_set(n, min);

        // its a fresh variable
        self.variables.push(VariableType::Primitive {
            index: evt_id,
            domain,
        });
        self.events.push(DomainEvent {
            variable,
            is_fixed: false,
            is_empty: false,
            min_changed: false,
            max_changed: false,
            domain_changed: false,
        });
        variable
    }

    fn min(&self, var: Variable) -> Option<isize> {
        let dom = self.primitive_domain(var);
        self.state
            .sparse_set_get_min(dom)
            .map(|value| self.primitive_to_view_value(var, value))
    }

    fn max(&self, var: Variable) -> Option<isize> {
        let dom = self.primitive_domain(var);
        self.state
            .sparse_set_get_max(dom)
            .map(|value| self.primitive_to_view_value(var, value))
    }

    fn size(&self, var: Variable) -> usize {
        let dom = self.primitive_domain(var);
        self.state.sparse_set_size(dom)
    }

    fn contains(&self, var: Variable, value: isize) -> bool {
        let vt = self.variables[var.0];
        match vt {
            VariableType::Primitive { domain, .. } => self.primitive_contains(value, domain),
            VariableType::OffsetView { x, offset } => self.contains(x, value - offset),
            VariableType::NegativeView { x } => self.contains(x, -value),
            VariableType::FlipView { x } => self.contains(x, if value == 0 { 1 } else { 0 }),
            VariableType::MultiplicationView { x, coeff } => {
                let q = value / coeff;
                if value != q * coeff {
                    false
                } else {
                    self.contains(x, q)
                }
            }
        }
    }

    fn fix(&mut self, var: Variable, value: isize) -> CPResult<()> {
        let vt = self.variables[var.0];
        match vt {
            VariableType::Primitive { index, domain } => self.primitive_fix(value, domain, index),
            VariableType::OffsetView { x, offset } => self.fix(x, value - offset),
            VariableType::NegativeView { x } => self.fix(x, -value),
            VariableType::FlipView { x } => self.fix(x, if value == 0 { 1 } else { 0 }),
            VariableType::MultiplicationView { x, coeff } => {
                let q = value / coeff;
                if value == q * coeff {
                    self.fix(x, q)
                } else {
                    let evt = self.event_index(var);
                    self.events[evt].min_changed = true;
                    self.events[evt].max_changed = true;
                    self.events[evt].domain_changed = true;
                    self.events[evt].is_empty = true;
                    Err(Inconsistency)
                }
            }
        }
    }

    fn remove(&mut self, var: Variable, value: isize) -> CPResult<()> {
        let vt = self.variables[var.0];
        match vt {
            VariableType::Primitive { index, domain } => {
                self.primitive_remove(value, domain, index)
            }
            VariableType::OffsetView { x, offset } => self.remove(x, value - offset),
            VariableType::NegativeView { x } => self.remove(x, -value),
            VariableType::FlipView { x } => self.remove(x, if value == 0 { 1 } else { 0 }),
            VariableType::MultiplicationView { x, coeff } => {
                let q = value / coeff;
                if value == q * coeff {
                    self.remove(x, q)
                } else {
                    Ok(())
                }
            }
        }
    }

    fn remove_below(&mut self, var: Variable, value: isize) -> CPResult<()> {
        let vt = self.variables[var.0];
        match vt {
            VariableType::Primitive { index, domain } => {
                self.primitive_remove_below(value, domain, index)
            }
            VariableType::OffsetView { x, offset } => self.remove_below(x, value - offset),
            VariableType::NegativeView { x } => self.remove_below(x, -value),
            VariableType::FlipView { x } => self.remove_below(x, if value == 0 { 1 } else { 0 }),
            VariableType::MultiplicationView { x, coeff } => {
                let q = value / coeff;
                let q = if value > 0 && q * coeff != value {
                    q + 1
                } else {
                    q
                };
                self.remove_below(x, q)
            }
        }
    }

    fn remove_above(&mut self, var: Variable, value: isize) -> CPResult<()> {
        let vt = self.variables[var.0];
        match vt {
            VariableType::Primitive { index, domain } => {
                self.primitive_remove_above(value, domain, index)
            }
            VariableType::OffsetView { x, offset } => self.remove_above(x, value - offset),
            VariableType::NegativeView { x } => self.remove_above(x, -value),
            VariableType::FlipView { x } => self.remove_above(x, if value == 0 { 1 } else { 0 }),
            VariableType::MultiplicationView { x, coeff } => {
                let q = value / coeff;
                let q = if value < 0 && q * coeff != value {
                    q - 1
                } else {
                    q
                };
                self.remove_above(x, q)
            }
        }
    }

    /// Returns a (view) variable corresponding to var * value
    fn mul(&mut self, var: Variable, coeff: isize) -> Variable {
        if coeff < 0 {
            let neg = self.neg(var);
            self.mul(neg, -coeff)
        } else {
            let id = (self.state.increment(self.n_vars) - 1) as usize;
            let variable = Variable(id);
            self.variables
                .push(VariableType::MultiplicationView { x: var, coeff });
            variable
        }
    }
    /// Returns a (view) variable corresponding to var + value
    fn plus(&mut self, var: Variable, value: isize) -> Variable {
        let id = (self.state.increment(self.n_vars) - 1) as usize;
        let variable = Variable(id);
        self.variables.push(VariableType::OffsetView {
            x: var,
            offset: value,
        });
        variable
    }
    /// Returns a (view) variable corresponding to var - value
    fn sub(&mut self, var: Variable, value: isize) -> Variable {
        self.plus(var, -value)
    }
    /// Returns a (view) variable corresponding to -var (flips the sign)
    fn neg(&mut self, var: Variable) -> Variable {
        let id = (self.state.increment(self.n_vars) - 1) as usize;
        let variable = Variable(id);
        self.variables.push(VariableType::NegativeView { x: var });
        variable
    }
    /// Returns a (view) variable corresponding to !var (flips the boolean polarity)
    fn not(&mut self, var: Variable) -> Variable {
        let id = (self.state.increment(self.n_vars) - 1) as usize;
        let variable = Variable(id);
        self.variables.push(VariableType::FlipView { x: var });
        variable
    }
}
impl<T: StateManager> SaveAndRestore for DomainStoreImpl<T> {
    fn save_state(&mut self) {
        self.state.save_state()
    }

    fn restore_state(&mut self) {
        self.state.restore_state();
        self.variables
            .truncate(self.state.get_int(self.n_vars) as usize);
        self.events
            .truncate(self.state.get_int(self.n_events) as usize);
    }
}
impl<T: StateManager> DomainBroker for DomainStoreImpl<T> {
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
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// private methods
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
impl<T: StateManager> DomainStoreImpl<T> {
    /// This method returns the source of truth of a variable. That is,
    /// for a primitive variable, it is the identity function and for views
    /// it returns the terminal primitive variable which this view is based on
    pub fn source_of_truth(&self, var: Variable) -> Variable {
        let vt = self.variables[var.0];
        match vt {
            VariableType::Primitive { .. } => var,
            VariableType::OffsetView { x, .. } => self.source_of_truth(x),
            VariableType::MultiplicationView { x, .. } => self.source_of_truth(x),
            VariableType::NegativeView { x } => self.source_of_truth(x),
            VariableType::FlipView { x } => self.source_of_truth(x),
        }
    }
    /// This method returns primitive domain of the variable; that is it returns
    /// the domain of the source of truth of the said variable.
    fn event_index(&self, var: Variable) -> usize {
        let vt = self.variables[var.0];
        match vt {
            VariableType::Primitive { index, .. } => index,
            VariableType::OffsetView { x, offset: _ } => self.event_index(x),
            VariableType::MultiplicationView { x, coeff: _ } => self.event_index(x),
            VariableType::NegativeView { x } => self.event_index(x),
            VariableType::FlipView { x } => self.event_index(x),
        }
    }
    /// This method returns primitive domain of the variable; that is it returns
    /// the domain of the source of truth of the said variable.
    fn primitive_domain(&self, var: Variable) -> ReversibleSparseSet {
        let vt = self.variables[var.0];
        match vt {
            VariableType::Primitive { domain, .. } => domain,
            VariableType::OffsetView { x, offset: _ } => self.primitive_domain(x),
            VariableType::MultiplicationView { x, coeff: _ } => self.primitive_domain(x),
            VariableType::NegativeView { x } => self.primitive_domain(x),
            VariableType::FlipView { x } => self.primitive_domain(x),
        }
    }

    /// This method performs the view function. It converts the
    /// given `value` from the primitive domain of var (var's source of truth
    /// domain) into a value in the domain of the view.
    fn primitive_to_view_value(&self, var: Variable, value: isize) -> isize {
        let vt = self.variables[var.0];
        match vt {
            VariableType::Primitive { .. } => value,
            VariableType::OffsetView { x, offset } => {
                self.primitive_to_view_value(x, value + offset)
            }
            VariableType::MultiplicationView { x, coeff } => {
                self.primitive_to_view_value(x, value * coeff)
            }
            VariableType::NegativeView { x } => self.primitive_to_view_value(x, -value),
            VariableType::FlipView { x } => {
                let newval = if value == 0 { 1 } else { 0 };
                self.primitive_to_view_value(x, newval)
            }
        }
    }
    /// Checks if a value is in the domain of a PRIMITIVE VAR whose dom is given
    fn primitive_contains(&self, value: isize, dom: ReversibleSparseSet) -> bool {
        self.state.sparse_set_contains(dom, value)
    }
    /// Fixes the value of a PRIMITIVE VAR whose domain and event id are given
    fn primitive_fix(
        &mut self,
        value: isize,
        dom: ReversibleSparseSet,
        evt: usize,
    ) -> CPResult<()> {
        if !self.primitive_contains(value, dom) {
            self.events[evt].min_changed = true;
            self.events[evt].max_changed = true;
            self.events[evt].domain_changed = true;
            self.events[evt].is_empty = true;
            CPResult::Err(Inconsistency)
        } else if self.state.sparse_set_size(dom) == 1 {
            // is fixed ?
            // if there is nothing to do, then we're done
            CPResult::Ok(())
        } else {
            let min_changed = self.state.sparse_set_get_min(dom) != Some(value);
            let max_changed = self.state.sparse_set_get_max(dom) != Some(value);
            self.state.sparse_set_remove_all_but(dom, value);
            if self.state.sparse_set_is_empty(dom) {
                self.events[evt].min_changed |= min_changed;
                self.events[evt].max_changed |= max_changed;
                self.events[evt].domain_changed = true;
                self.events[evt].is_empty = true;
                CPResult::Err(Inconsistency)
            } else {
                self.events[evt].min_changed |= min_changed;
                self.events[evt].max_changed |= max_changed;
                self.events[evt].domain_changed = true;
                self.events[evt].is_fixed = true;
                CPResult::Ok(())
            }
        }
    }
    /// Removes a single value from the domain of a PRIMITIVE VAR
    fn primitive_remove(
        &mut self,
        value: isize,
        dom: ReversibleSparseSet,
        evt: usize,
    ) -> CPResult<()> {
        if !self.primitive_contains(value, dom) {
            // there is nothing to do
            CPResult::Ok(())
        } else {
            let min_changed = self.state.sparse_set_get_min(dom) == Some(value);
            let max_changed = self.state.sparse_set_get_max(dom) == Some(value);

            let domain_changed = self.state.sparse_set_remove(dom, value);
            let size = self.state.sparse_set_size(dom);
            let is_fixed = size == 1;
            let is_empty = size == 0;

            self.events[evt].min_changed |= min_changed;
            self.events[evt].max_changed |= max_changed;
            self.events[evt].is_fixed |= is_fixed;
            self.events[evt].is_empty |= is_empty;
            self.events[evt].domain_changed |= domain_changed;

            if is_empty {
                CPResult::Err(Inconsistency)
            } else {
                CPResult::Ok(())
            }
        }
    }
    /// Removes all candidates less than a given value from the domain of a
    /// PRIMITIVE VARIABLE
    fn primitive_remove_below(
        &mut self,
        value: isize,
        dom: ReversibleSparseSet,
        evt: usize,
    ) -> CPResult<()> {
        let min_changed = self.state.sparse_set_get_min(dom) < Some(value);
        if min_changed {
            self.state.sparse_set_remove_below(dom, value);
            let size = self.state.sparse_set_size(dom);

            match size {
                0 => {
                    self.events[evt].is_empty = true;
                    CPResult::Err(Inconsistency)
                }
                1 => {
                    self.events[evt].is_fixed = true;
                    self.events[evt].min_changed = true;
                    self.events[evt].domain_changed = true;
                    CPResult::Ok(())
                }
                _ => {
                    self.events[evt].min_changed = true;
                    self.events[evt].domain_changed = true;
                    CPResult::Ok(())
                }
            }
        } else {
            // Nothing to do
            CPResult::Ok(())
        }
    }
    /// Removes all candidates greater than a given value from the domain of a
    /// PRIMITIVE VARIABLE
    fn primitive_remove_above(
        &mut self,
        value: isize,
        dom: ReversibleSparseSet,
        evt: usize,
    ) -> CPResult<()> {
        let max_changed = self.state.sparse_set_get_max(dom) > Some(value);
        if max_changed {
            self.state.sparse_set_remove_above(dom, value);
            let size = self.state.sparse_set_size(dom);

            match size {
                0 => {
                    self.events[evt].is_empty = true;
                    CPResult::Err(Inconsistency)
                }
                1 => {
                    self.events[evt].is_fixed = true;
                    self.events[evt].max_changed = true;
                    self.events[evt].domain_changed = true;
                    CPResult::Ok(())
                }
                _ => {
                    self.events[evt].max_changed = true;
                    self.events[evt].domain_changed = true;
                    CPResult::Ok(())
                }
            }
        } else {
            // Nothing to do
            CPResult::Ok(())
        }
    }
}

// #############################################################################
// ### UNIT TESTS ##############################################################
// #############################################################################
#[cfg(test)]
mod test_domainstoreimpl_saveandrestore {
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
}
#[cfg(test)]
mod test_domainstoreimpl_domainbroker {
    use super::*;

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
mod test_domainstoreimpl_domainstore_primitive_var {
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
            ds.events[ds.event_index(x)],
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
            ds.events[ds.event_index(y)],
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
            ds.events[ds.event_index(z)],
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
            ds.events[ds.event_index(x)],
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
            ds.events[ds.event_index(y)],
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
            ds.events[ds.event_index(z)],
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
            ds.events[ds.event_index(x)],
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
            ds.events[ds.event_index(y)],
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
            ds.events[ds.event_index(z)],
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
            ds.events[ds.event_index(x)],
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
            ds.events[ds.event_index(y)],
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
            ds.events[ds.event_index(z)],
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
            ds.events[ds.event_index(x)],
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
            ds.events[ds.event_index(y)],
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
            ds.events[ds.event_index(z)],
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
            ds.events[ds.event_index(x)],
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
            ds.events[ds.event_index(y)],
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
            ds.events[ds.event_index(z)],
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
            ds.events[ds.event_index(x)],
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
            ds.events[ds.event_index(y)],
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
            ds.events[ds.event_index(z)],
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
            ds.events[ds.event_index(x)],
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
            ds.events[ds.event_index(y)],
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
            ds.events[ds.event_index(z)],
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
            ds.events[ds.event_index(x)],
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
            ds.events[ds.event_index(y)],
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
            ds.events[ds.event_index(z)],
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
            ds.events[ds.event_index(x)],
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
            ds.events[ds.event_index(y)],
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
            ds.events[ds.event_index(z)],
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
            ds.events[ds.event_index(x)],
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
            ds.events[ds.event_index(y)],
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
            ds.events[ds.event_index(z)],
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
            ds.events[ds.event_index(x)],
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
            ds.events[ds.event_index(y)],
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
            ds.events[ds.event_index(z)],
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

#[cfg(test)]
mod test_domainstoreimpl_domainstore_mul_view {
    use super::*;

    #[test]
    fn min_yields_the_minimum_of_domain() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Some(10), ds.min(x));
        assert_eq!(Some(0), ds.min(y));
        assert_eq!(Some(0), ds.min(z));
    }
    #[test]
    fn min_yields_the_minimum_of_domain_after_update() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, 14));
        assert_eq!(Ok(()), ds.remove_below(y, 6));
        assert_eq!(Ok(()), ds.remove_below(z, 2));

        assert_eq!(Some(14), ds.min(x));
        assert_eq!(Some(6), ds.min(y));
        assert_eq!(Some(2), ds.min(z));
    }
    #[test]
    fn min_yields_none_when_domain_is_empty() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Err(Inconsistency), ds.remove_below(x, 40));
        assert_eq!(Err(Inconsistency), ds.remove_below(y, 40));
        assert_eq!(Err(Inconsistency), ds.remove_below(z, 40));

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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Some(20), ds.max(x));
        assert_eq!(Some(10), ds.max(y));
        assert_eq!(Some(2), ds.max(z));
    }
    #[test]
    fn max_yields_the_maximum_of_domain_after_update() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove_above(x, 14));
        assert_eq!(Ok(()), ds.remove_above(y, 6));
        assert_eq!(Ok(()), ds.remove_above(z, 0));

        assert_eq!(Some(14), ds.max(x));
        assert_eq!(Some(6), ds.max(y));
        assert_eq!(Some(0), ds.max(z));
    }
    #[test]
    fn max_yields_none_when_domain_is_empty() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 14));
        assert_eq!(Ok(()), ds.remove(y, 6));
        assert_eq!(Ok(()), ds.remove(z, 2));

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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, 14));
        assert_eq!(Ok(()), ds.remove_below(y, 6));
        assert_eq!(Ok(()), ds.remove_below(z, 2));

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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove_above(x, 14));
        assert_eq!(Ok(()), ds.remove_above(y, 6));
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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert!(ds.contains(x, 10));
        assert!(ds.contains(y, 0));
        assert!(ds.contains(z, 0));
    }
    #[test]
    fn contains_returns_false_for_value_gt_than_ub() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert!(ds.contains(x, 20));
        assert!(ds.contains(y, 10));
        assert!(ds.contains(z, 2));
    }
    #[test]
    fn contains_returns_false_for_hole() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 14));
        assert_eq!(Ok(()), ds.remove(y, 6));
        assert_eq!(Ok(()), ds.remove(z, 0));

        assert!(!ds.contains(x, 14));
        assert!(!ds.contains(y, 6));
        assert!(!ds.contains(z, 0));
    }
    #[test]
    fn contains_returns_true_if_in_set() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 14));
        assert_eq!(Ok(()), ds.remove(y, 6));
        assert_eq!(Ok(()), ds.remove(z, 0));

        assert!(ds.contains(x, 12));
        assert!(ds.contains(y, 4));
        assert!(ds.contains(z, 2));
    }

    #[test]
    fn fix_fails_when_lower_than_lb() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Err(Inconsistency), ds.fix(x, 40));
        assert_eq!(Err(Inconsistency), ds.fix(y, 40));
        assert_eq!(Err(Inconsistency), ds.fix(z, 40));
    }
    #[test]
    fn fix_fails_when_hole() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 14));
        assert_eq!(Ok(()), ds.remove(y, 6));
        assert_eq!(Ok(()), ds.remove(z, 0));

        assert_eq!(Err(Inconsistency), ds.fix(x, 14));
        assert_eq!(Err(Inconsistency), ds.fix(y, 6));
        assert_eq!(Err(Inconsistency), ds.fix(z, 0));
    }
    #[test]
    fn fix_succeeds_when_in_domain() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.fix(x, 14));
        assert_eq!(Ok(()), ds.fix(y, 6));
        assert_eq!(Ok(()), ds.fix(z, 0));
    }
    #[test]
    fn fix_sets_events() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.fix(x, 14));
        assert_eq!(Ok(()), ds.fix(y, 6));
        assert_eq!(Ok(()), ds.fix(z, 0));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: true,
                is_empty: false,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: true,
                is_empty: false,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove(x, -20));
        assert_eq!(Ok(()), ds.remove(y, -20));
        assert_eq!(Ok(()), ds.remove(z, -20));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, 14));
        assert_eq!(Ok(()), ds.remove_below(y, 6));
        assert_eq!(Ok(()), ds.remove_below(z, 0));

        assert_eq!(Ok(()), ds.remove_above(x, 14));
        assert_eq!(Ok(()), ds.remove_above(y, 6));
        assert_eq!(Ok(()), ds.remove_above(z, 0));

        assert_eq!(Err(Inconsistency), ds.remove(x, 14));
        assert_eq!(Err(Inconsistency), ds.remove(y, 6));
        assert_eq!(Err(Inconsistency), ds.remove(z, 0));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: true,
                is_empty: true,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: true,
                is_empty: true,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 14));
        assert_eq!(Ok(()), ds.remove(y, 6));
        assert_eq!(Ok(()), ds.remove(z, 0));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 10));
        assert_eq!(Ok(()), ds.remove(y, 0));
        assert_eq!(Ok(()), ds.remove(z, 0));

        assert_eq!(Some(12), ds.min(x));
        assert_eq!(Some(2), ds.min(y));
        assert_eq!(Some(2), ds.min(z));

        assert_eq!(Some(20), ds.max(x));
        assert_eq!(Some(10), ds.max(y));
        assert_eq!(Some(2), ds.max(z));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 20));
        assert_eq!(Ok(()), ds.remove(y, 10));
        assert_eq!(Ok(()), ds.remove(z, 2));

        assert_eq!(Some(10), ds.min(x));
        assert_eq!(Some(0), ds.min(y));
        assert_eq!(Some(0), ds.min(z));

        assert_eq!(Some(18), ds.max(x));
        assert_eq!(Some(8), ds.max(y));
        assert_eq!(Some(0), ds.max(z));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove_above(x, 40));
        assert_eq!(Ok(()), ds.remove_above(y, 40));
        assert_eq!(Ok(()), ds.remove_above(z, 40));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Err(Inconsistency), ds.remove_above(x, -20));
        assert_eq!(Err(Inconsistency), ds.remove_above(y, -20));
        assert_eq!(Err(Inconsistency), ds.remove_above(z, -20));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove_above(x, 14));
        assert_eq!(Ok(()), ds.remove_above(y, 6));
        assert_eq!(Ok(()), ds.remove_above(z, 0));

        assert_eq!(Some(10), ds.min(x));
        assert_eq!(Some(0), ds.min(y));
        assert_eq!(Some(0), ds.min(z));

        assert_eq!(Some(14), ds.max(x));
        assert_eq!(Some(6), ds.max(y));
        assert_eq!(Some(0), ds.max(z));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, -40));
        assert_eq!(Ok(()), ds.remove_below(y, -40));
        assert_eq!(Ok(()), ds.remove_below(z, -40));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Err(Inconsistency), ds.remove_below(x, 40));
        assert_eq!(Err(Inconsistency), ds.remove_below(y, 40));
        assert_eq!(Err(Inconsistency), ds.remove_below(z, 40));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, 14));
        assert_eq!(Ok(()), ds.remove_below(y, 6));
        assert_eq!(Ok(()), ds.remove_below(z, 2));

        assert_eq!(Some(14), ds.min(x));
        assert_eq!(Some(6), ds.min(y));
        assert_eq!(Some(2), ds.min(z));

        assert_eq!(Some(20), ds.max(x));
        assert_eq!(Some(10), ds.max(y));
        assert_eq!(Some(2), ds.max(z));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.mul(x, 2);
        let y = ds.mul(y, 2);
        let z = ds.mul(z, 2);

        assert!(!ds.is_fixed(x));
        assert!(!ds.is_fixed(y));
        assert!(!ds.is_fixed(z));
        ds.save_state();

        assert_eq!(Ok(()), ds.fix(x, 14));
        assert_eq!(Ok(()), ds.fix(y, 6));
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
    fn contains_is_false_if_not_in_underlying_domain() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let x = ds.mul(x, 2);

        assert!(!ds.contains(x, 13));
    }

    #[test]
    fn fix_fails_on_nonexistent_value() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let x = ds.mul(x, 2);

        assert_eq!(Err(Inconsistency), ds.fix(x, 13));
    }
    #[test]
    fn remove_below_ceils_the_value() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let x = ds.mul(x, 2);

        assert_eq!(Ok(()), ds.remove_below(x, 13));
        assert_eq!(Some(14), ds.min(x));
    }
    #[test]
    fn remove_above_floors_the_value() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let x = ds.mul(x, 2);

        assert_eq!(Ok(()), ds.remove_above(x, 13));
        assert_eq!(Some(12), ds.max(x));
    }
    #[test]
    fn remove_above_floors_the_value_negative_coeff() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10); //   5   6   7   8   9  10
        let x = ds.mul(x, -2); // -20 -18 -16 -14 -12 -10
        assert_eq!(Ok(()), ds.remove_above(x, -13)); // -20 -18 -16 -14
        assert_eq!(Some(-14), ds.max(x));
    }

    #[test]
    fn remove_above_floors_the_value_negative_coeff_positive_value() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10); //   5   6   7   8   9  10
        let x = ds.mul(x, -2); // -20 -18 -16 -14 -12 -10
        assert_eq!(Err(Inconsistency), ds.remove_above(x, 0)); // empty set
    }
}

#[cfg(test)]
mod test_domainstoreimpl_domainstore_plus_view {
    use super::*;

    #[test]
    fn min_yields_the_minimum_of_domain() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Some(7), ds.min(x));
        assert_eq!(Some(2), ds.min(y));
        assert_eq!(Some(2), ds.min(z));
    }
    #[test]
    fn min_yields_the_minimum_of_domain_after_update() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, 9));
        assert_eq!(Ok(()), ds.remove_below(y, 5));
        assert_eq!(Ok(()), ds.remove_below(z, 3));

        assert_eq!(Some(9), ds.min(x));
        assert_eq!(Some(5), ds.min(y));
        assert_eq!(Some(3), ds.min(z));
    }
    #[test]
    fn min_yields_none_when_domain_is_empty() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Err(Inconsistency), ds.remove_below(x, 40));
        assert_eq!(Err(Inconsistency), ds.remove_below(y, 40));
        assert_eq!(Err(Inconsistency), ds.remove_below(z, 40));

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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Some(12), ds.max(x));
        assert_eq!(Some(7), ds.max(y));
        assert_eq!(Some(3), ds.max(z));
    }
    #[test]
    fn max_yields_the_maximum_of_domain_after_update() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove_above(x, 9));
        assert_eq!(Ok(()), ds.remove_above(y, 5));
        assert_eq!(Ok(()), ds.remove_above(z, 2));

        assert_eq!(Some(9), ds.max(x));
        assert_eq!(Some(5), ds.max(y));
        assert_eq!(Some(2), ds.max(z));
    }
    #[test]
    fn max_yields_none_when_domain_is_empty() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 9));
        assert_eq!(Ok(()), ds.remove(y, 5));
        assert_eq!(Ok(()), ds.remove(z, 3));

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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, 9));
        assert_eq!(Ok(()), ds.remove_below(y, 5));
        assert_eq!(Ok(()), ds.remove_below(z, 3));

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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove_above(x, 9));
        assert_eq!(Ok(()), ds.remove_above(y, 5));
        assert_eq!(Ok(()), ds.remove_above(z, 2));

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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert!(ds.contains(x, 7));
        assert!(ds.contains(y, 2));
        assert!(ds.contains(z, 2));
    }
    #[test]
    fn contains_returns_false_for_value_gt_than_ub() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert!(ds.contains(x, 12));
        assert!(ds.contains(y, 7));
        assert!(ds.contains(z, 3));
    }
    #[test]
    fn contains_returns_false_for_hole() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 9));
        assert_eq!(Ok(()), ds.remove(y, 5));
        assert_eq!(Ok(()), ds.remove(z, 2));

        assert!(!ds.contains(x, 9));
        assert!(!ds.contains(y, 5));
        assert!(!ds.contains(z, 2));
    }
    #[test]
    fn contains_returns_true_if_in_set() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 9));
        assert_eq!(Ok(()), ds.remove(y, 5));
        assert_eq!(Ok(()), ds.remove(z, 2));

        assert!(ds.contains(x, 8));
        assert!(ds.contains(y, 4));
        assert!(ds.contains(z, 3));
    }

    #[test]
    fn fix_fails_when_lower_than_lb() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Err(Inconsistency), ds.fix(x, 40));
        assert_eq!(Err(Inconsistency), ds.fix(y, 40));
        assert_eq!(Err(Inconsistency), ds.fix(z, 40));
    }
    #[test]
    fn fix_fails_when_hole() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 9));
        assert_eq!(Ok(()), ds.remove(y, 5));
        assert_eq!(Ok(()), ds.remove(z, 2));

        assert_eq!(Err(Inconsistency), ds.fix(x, 9));
        assert_eq!(Err(Inconsistency), ds.fix(y, 5));
        assert_eq!(Err(Inconsistency), ds.fix(z, 2));
    }
    #[test]
    fn fix_succeeds_when_in_domain() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.fix(x, 9));
        assert_eq!(Ok(()), ds.fix(y, 5));
        assert_eq!(Ok(()), ds.fix(z, 2));
    }
    #[test]
    fn fix_sets_events() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.fix(x, 9));
        assert_eq!(Ok(()), ds.fix(y, 5));
        assert_eq!(Ok(()), ds.fix(z, 2));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: true,
                is_empty: false,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: true,
                is_empty: false,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove(x, -20));
        assert_eq!(Ok(()), ds.remove(y, -20));
        assert_eq!(Ok(()), ds.remove(z, -20));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, 9));
        assert_eq!(Ok(()), ds.remove_below(y, 5));
        assert_eq!(Ok(()), ds.remove_below(z, 2));

        assert_eq!(Ok(()), ds.remove_above(x, 9));
        assert_eq!(Ok(()), ds.remove_above(y, 5));
        assert_eq!(Ok(()), ds.remove_above(z, 2));

        assert_eq!(Err(Inconsistency), ds.remove(x, 9));
        assert_eq!(Err(Inconsistency), ds.remove(y, 5));
        assert_eq!(Err(Inconsistency), ds.remove(z, 2));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: true,
                is_empty: true,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: true,
                is_empty: true,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 9));
        assert_eq!(Ok(()), ds.remove(y, 5));
        assert_eq!(Ok(()), ds.remove(z, 2));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 7));
        assert_eq!(Ok(()), ds.remove(y, 2));
        assert_eq!(Ok(()), ds.remove(z, 2));

        assert_eq!(Some(8), ds.min(x));
        assert_eq!(Some(3), ds.min(y));
        assert_eq!(Some(3), ds.min(z));

        assert_eq!(Some(12), ds.max(x));
        assert_eq!(Some(7), ds.max(y));
        assert_eq!(Some(3), ds.max(z));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 12));
        assert_eq!(Ok(()), ds.remove(y, 7));
        assert_eq!(Ok(()), ds.remove(z, 3));

        assert_eq!(Some(7), ds.min(x));
        assert_eq!(Some(2), ds.min(y));
        assert_eq!(Some(2), ds.min(z));

        assert_eq!(Some(11), ds.max(x));
        assert_eq!(Some(6), ds.max(y));
        assert_eq!(Some(2), ds.max(z));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove_above(x, 40));
        assert_eq!(Ok(()), ds.remove_above(y, 40));
        assert_eq!(Ok(()), ds.remove_above(z, 40));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Err(Inconsistency), ds.remove_above(x, -20));
        assert_eq!(Err(Inconsistency), ds.remove_above(y, -20));
        assert_eq!(Err(Inconsistency), ds.remove_above(z, -20));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove_above(x, 9));
        assert_eq!(Ok(()), ds.remove_above(y, 5));
        assert_eq!(Ok(()), ds.remove_above(z, 2));

        assert_eq!(Some(7), ds.min(x));
        assert_eq!(Some(2), ds.min(y));
        assert_eq!(Some(2), ds.min(z));

        assert_eq!(Some(9), ds.max(x));
        assert_eq!(Some(5), ds.max(y));
        assert_eq!(Some(2), ds.max(z));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, -40));
        assert_eq!(Ok(()), ds.remove_below(y, -40));
        assert_eq!(Ok(()), ds.remove_below(z, -40));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Err(Inconsistency), ds.remove_below(x, 40));
        assert_eq!(Err(Inconsistency), ds.remove_below(y, 40));
        assert_eq!(Err(Inconsistency), ds.remove_below(z, 40));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, 9));
        assert_eq!(Ok(()), ds.remove_below(y, 5));
        assert_eq!(Ok(()), ds.remove_below(z, 3));

        assert_eq!(Some(9), ds.min(x));
        assert_eq!(Some(5), ds.min(y));
        assert_eq!(Some(3), ds.min(z));

        assert_eq!(Some(12), ds.max(x));
        assert_eq!(Some(7), ds.max(y));
        assert_eq!(Some(3), ds.max(z));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.plus(x, 2);
        let y = ds.plus(y, 2);
        let z = ds.plus(z, 2);

        assert!(!ds.is_fixed(x));
        assert!(!ds.is_fixed(y));
        assert!(!ds.is_fixed(z));
        ds.save_state();

        assert_eq!(Ok(()), ds.fix(x, 9));
        assert_eq!(Ok(()), ds.fix(y, 5));
        assert_eq!(Ok(()), ds.fix(z, 2));
        assert!(ds.is_fixed(x));
        assert!(ds.is_fixed(y));
        assert!(ds.is_fixed(z));
        ds.restore_state();

        assert!(!ds.is_fixed(x));
        assert!(!ds.is_fixed(y));
        assert!(!ds.is_fixed(z));
    }
}

#[cfg(test)]
mod test_domainstoreimpl_domainstore_sub_view {
    use super::*;

    #[test]
    fn min_yields_the_minimum_of_domain() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Some(3), ds.min(x));
        assert_eq!(Some(-2), ds.min(y));
        assert_eq!(Some(-2), ds.min(z));
    }
    #[test]
    fn min_yields_the_minimum_of_domain_after_update() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, 5));
        assert_eq!(Ok(()), ds.remove_below(y, 1));
        assert_eq!(Ok(()), ds.remove_below(z, -1));

        assert_eq!(Some(5), ds.min(x));
        assert_eq!(Some(1), ds.min(y));
        assert_eq!(Some(-1), ds.min(z));
    }
    #[test]
    fn min_yields_none_when_domain_is_empty() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Err(Inconsistency), ds.remove_below(x, 40));
        assert_eq!(Err(Inconsistency), ds.remove_below(y, 40));
        assert_eq!(Err(Inconsistency), ds.remove_below(z, 40));

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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Some(8), ds.max(x));
        assert_eq!(Some(3), ds.max(y));
        assert_eq!(Some(-1), ds.max(z));
    }
    #[test]
    fn max_yields_the_maximum_of_domain_after_update() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove_above(x, 5));
        assert_eq!(Ok(()), ds.remove_above(y, 1));
        assert_eq!(Ok(()), ds.remove_above(z, -2));

        assert_eq!(Some(5), ds.max(x));
        assert_eq!(Some(1), ds.max(y));
        assert_eq!(Some(-2), ds.max(z));
    }
    #[test]
    fn max_yields_none_when_domain_is_empty() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Err(Inconsistency), ds.remove_above(x, -10));
        assert_eq!(Err(Inconsistency), ds.remove_above(y, -10));
        assert_eq!(Err(Inconsistency), ds.remove_above(z, -10));

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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 5));
        assert_eq!(Ok(()), ds.remove(y, 3));
        assert_eq!(Ok(()), ds.remove(z, -1));

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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, 5));
        assert_eq!(Ok(()), ds.remove_below(y, 1));
        assert_eq!(Ok(()), ds.remove_below(z, -1));

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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove_above(x, 5));
        assert_eq!(Ok(()), ds.remove_above(y, 1));
        assert_eq!(Ok(()), ds.remove_above(z, -2));

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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert!(!ds.contains(x, -15));
        assert!(!ds.contains(y, -15));
        assert!(!ds.contains(z, -15));
    }
    #[test]
    fn contains_returns_true_for_lb() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert!(ds.contains(x, 3));
        assert!(ds.contains(y, -2));
        assert!(ds.contains(z, -2));
    }
    #[test]
    fn contains_returns_false_for_value_gt_than_ub() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert!(ds.contains(x, 8));
        assert!(ds.contains(y, 3));
        assert!(ds.contains(z, -1));
    }
    #[test]
    fn contains_returns_false_for_hole() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 5));
        assert_eq!(Ok(()), ds.remove(y, 1));
        assert_eq!(Ok(()), ds.remove(z, -2));

        assert!(!ds.contains(x, 9));
        assert!(!ds.contains(y, 5));
        assert!(!ds.contains(z, 2));
    }

    #[test]
    fn contains_returns_true_if_in_set() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 5));
        assert_eq!(Ok(()), ds.remove(y, 1));
        assert_eq!(Ok(()), ds.remove(z, -1));

        assert!(ds.contains(x, 4));
        assert!(ds.contains(y, 0));
        assert!(ds.contains(z, -2));
    }

    #[test]
    fn fix_fails_when_lower_than_lb() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Err(Inconsistency), ds.fix(x, 40));
        assert_eq!(Err(Inconsistency), ds.fix(y, 40));
        assert_eq!(Err(Inconsistency), ds.fix(z, 40));
    }

    #[test]
    fn fix_fails_when_hole() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 5));
        assert_eq!(Ok(()), ds.remove(y, 1));
        assert_eq!(Ok(()), ds.remove(z, -1));

        assert_eq!(Err(Inconsistency), ds.fix(x, 5));
        assert_eq!(Err(Inconsistency), ds.fix(y, 1));
        assert_eq!(Err(Inconsistency), ds.fix(z, -1));
    }
    #[test]
    fn fix_succeeds_when_in_domain() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.fix(x, 5));
        assert_eq!(Ok(()), ds.fix(y, 1));
        assert_eq!(Ok(()), ds.fix(z, -1));
    }
    #[test]
    fn fix_sets_events() {
        let mut ds = DefaultDomainStore::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.fix(x, 5));
        assert_eq!(Ok(()), ds.fix(y, 1));
        assert_eq!(Ok(()), ds.fix(z, -1));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: true,
                is_empty: false,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: true,
                is_empty: false,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
                is_fixed: true,
                is_empty: false,
                min_changed: true,
                max_changed: false,
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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove(x, -20));
        assert_eq!(Ok(()), ds.remove(y, -20));
        assert_eq!(Ok(()), ds.remove(z, -20));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, 5));
        assert_eq!(Ok(()), ds.remove_below(y, 1));
        assert_eq!(Ok(()), ds.remove_below(z, -1));

        assert_eq!(Ok(()), ds.remove_above(x, 5));
        assert_eq!(Ok(()), ds.remove_above(y, 1));
        assert_eq!(Ok(()), ds.remove_above(z, -1));

        assert_eq!(Err(Inconsistency), ds.remove(x, 5));
        assert_eq!(Err(Inconsistency), ds.remove(y, 1));
        assert_eq!(Err(Inconsistency), ds.remove(z, -1));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: true,
                is_empty: true,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: true,
                is_empty: true,
                min_changed: true,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 5));
        assert_eq!(Ok(()), ds.remove(y, 1));
        assert_eq!(Ok(()), ds.remove(z, -1));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
                is_fixed: true,
                is_empty: false,
                min_changed: false,
                max_changed: true,
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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 3));
        assert_eq!(Ok(()), ds.remove(y, -2));
        assert_eq!(Ok(()), ds.remove(z, -2));

        assert_eq!(Some(4), ds.min(x));
        assert_eq!(Some(-1), ds.min(y));
        assert_eq!(Some(-1), ds.min(z));

        assert_eq!(Some(8), ds.max(x));
        assert_eq!(Some(3), ds.max(y));
        assert_eq!(Some(-1), ds.max(z));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove(x, 8));
        assert_eq!(Ok(()), ds.remove(y, 3));
        assert_eq!(Ok(()), ds.remove(z, -1));

        assert_eq!(Some(3), ds.min(x));
        assert_eq!(Some(-2), ds.min(y));
        assert_eq!(Some(-2), ds.min(z));

        assert_eq!(Some(7), ds.max(x));
        assert_eq!(Some(2), ds.max(y));
        assert_eq!(Some(-2), ds.max(z));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove_above(x, 40));
        assert_eq!(Ok(()), ds.remove_above(y, 40));
        assert_eq!(Ok(()), ds.remove_above(z, 40));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Err(Inconsistency), ds.remove_above(x, -20));
        assert_eq!(Err(Inconsistency), ds.remove_above(y, -20));
        assert_eq!(Err(Inconsistency), ds.remove_above(z, -20));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove_above(x, 5));
        assert_eq!(Ok(()), ds.remove_above(y, 1));
        assert_eq!(Ok(()), ds.remove_above(z, -2));

        assert_eq!(Some(3), ds.min(x));
        assert_eq!(Some(-2), ds.min(y));
        assert_eq!(Some(-2), ds.min(z));

        assert_eq!(Some(5), ds.max(x));
        assert_eq!(Some(1), ds.max(y));
        assert_eq!(Some(-2), ds.max(z));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: true,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, -40));
        assert_eq!(Ok(()), ds.remove_below(y, -40));
        assert_eq!(Ok(()), ds.remove_below(z, -40));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Err(Inconsistency), ds.remove_below(x, 40));
        assert_eq!(Err(Inconsistency), ds.remove_below(y, 40));
        assert_eq!(Err(Inconsistency), ds.remove_below(z, 40));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: true,
                min_changed: false,
                max_changed: false,
                domain_changed: false,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert_eq!(Ok(()), ds.remove_below(x, 5));
        assert_eq!(Ok(()), ds.remove_below(y, 1));
        assert_eq!(Ok(()), ds.remove_below(z, -1));

        assert_eq!(Some(5), ds.min(x));
        assert_eq!(Some(1), ds.min(y));
        assert_eq!(Some(-1), ds.min(z));

        assert_eq!(Some(8), ds.max(x));
        assert_eq!(Some(3), ds.max(y));
        assert_eq!(Some(-1), ds.max(z));

        assert_eq!(
            ds.events[ds.event_index(x)],
            DomainEvent {
                variable: ds.source_of_truth(x),
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(y)],
            DomainEvent {
                variable: ds.source_of_truth(y),
                is_fixed: false,
                is_empty: false,
                min_changed: true,
                max_changed: false,
                domain_changed: true,
            }
        );
        assert_eq!(
            ds.events[ds.event_index(z)],
            DomainEvent {
                variable: ds.source_of_truth(z),
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

        let x = ds.sub(x, 2);
        let y = ds.sub(y, 2);
        let z = ds.sub(z, 2);

        assert!(!ds.is_fixed(x));
        assert!(!ds.is_fixed(y));
        assert!(!ds.is_fixed(z));
        ds.save_state();

        assert_eq!(Ok(()), ds.fix(x, 5));
        assert_eq!(Ok(()), ds.fix(y, 1));
        assert_eq!(Ok(()), ds.fix(z, -2));
        assert!(ds.is_fixed(x));
        assert!(ds.is_fixed(y));
        assert!(ds.is_fixed(z));
        ds.restore_state();

        assert!(!ds.is_fixed(x));
        assert!(!ds.is_fixed(y));
        assert!(!ds.is_fixed(z));
    }
}
