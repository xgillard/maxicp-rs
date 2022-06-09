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

//! This module provides the definition and implementation of the traits and
//! structure related to the constraint propagation.

use std::collections::hash_map::Entry;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    DomainBroker, DomainStoreImpl, ReversibleInt, SaveAndRestore, StateManager,
    TrailedStateManager, Variable,
};

use super::{CPResult, DomainStore};

/// This trait stands for the modeling constructs which you'll want to work
/// with when representing the problem you intend to solve. These modeling
/// constructs are often referred to as constraints, but this implementation
/// reserves the constraint type for an atomic constraint associated with
/// a propagator.
pub trait ModelingConstruct {
    /// This method installs the current modeling construct (which might
    /// consist of several underlying propagators/constraints) into the
    /// constraint store which will schedule its propagators as needed.
    fn install(&self, constraint_store: &mut dyn ConstraintStore);
}

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

/// Any closure/function that accepts a mutable ref to the domain store can be
/// a propagator. (This is mere convenience, not required to get something
/// useable)
impl<F: FnMut(&mut dyn DomainStore) -> CPResult<()>> Propagator for F {
    fn propagate(&mut self, domain_store: &mut dyn DomainStore) -> CPResult<()> {
        self(domain_store)
    }
}

/// A condition expressing that a specific change event has occurred on the
/// domain of some variable
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DomainCondition {
    /// This condidion is satisfied whenever the domain of a variable becomes
    /// fixed
    IsFixed(Variable),
    /// The minimum value of the domain has changed
    MinimumChanged(Variable),
    /// The maximum value of the domain has changed
    MaximumChanged(Variable),
    /// This condition is satisfied when +something+ has changed in the domain
    /// of the variable
    DomainChanged(Variable),
}

/// A constraint store is the entity responsible for storing the constraints
/// (hence the name), enforcing the consistency of these constraints using
/// propagators when the domains of the variables change.
pub trait ConstraintStore {
    /// Installs a given modeling constuct into the constraint store
    fn install(&mut self, modeling_construct: &dyn ModelingConstruct);
    /// Posts the given propagator but does  
    fn post(&mut self, propagator: Box<dyn Propagator>) -> Constraint;
    /// Tells the solver that the given constraint should be propagated whenever
    /// the condition is satisfied
    fn propagate_on(&mut self, constraint: Constraint, cond: DomainCondition);
    /// Propagate all constraints until a fixpoint is reached
    fn fixpoint(&mut self) -> CPResult<()>;
}

/// The basic expectation of a CP model is that it lets us create variables
/// (hence the DomainStore responsibility), install constraints bearing on
/// these variables (hence the ConstraintStore responsibility) and that its
/// state can be efficiently saved and restored to a previous snapshot during
/// the search for a satisfying -- or optimal -- solution (hence the
/// SaveAndRestore responsibility). A CP model *must* implement all three of
/// these responsibilities in order to match common expectations.
pub trait CpModel: DomainStore + ConstraintStore + SaveAndRestore {}

/// This is the type of the CP model you will likely want to work with. \
/// Currently, this is the only available implementation of a CP Model, but it
/// *might* possibly change in the future.
pub type DefaultCpModel = CpModelImpl<TrailedStateManager>;

/// This is the type of constraint store implementation you will likely want to
/// use in your solver. Currently, this is the only available implementation of
/// a CS but it *might* possibly change in the future.
pub type DefaultConstraintStore = DefaultCpModel;

/// This is a simple implementation of a constraint store.
///
/// # Note
/// Because it would be very inconvenient to always force a client to go through
/// the domain store of the constraint store, I let this struct be a domain
/// store with save and restore capabilities. The implementation of these traits
/// is simply delegated to another structure that actually implements some
/// business logic for it.
pub struct CpModelImpl<T: StateManager> {
    /// The domain store which is used to manage the problem variables
    domains: DomainStoreImpl<T>,
    /// This establishes a correspondence between a domain condition and all
    /// the porpagators that need to be scheduled
    listeners: FxHashMap<DomainCondition, FxHashSet<Constraint>>,

    /// These are the propagators that might be used to effectively trim down
    /// the variable domains
    propagators: Vec<Box<dyn Propagator>>,
    /// This list tracks the associations that have been made between a domain
    /// condition and a propagator. The whole point of keeping this list is to
    /// be able to undo the associations upon state restoration (in conjunction
    /// with the conditions_sz field)
    conditions: Vec<(DomainCondition, Constraint)>,
    /// This tracks the length of the propagators that are active at any given
    /// point in time. The point of this variable is to be able to drop the
    /// propagators as soon as they are no longer required.
    propagator_sz: ReversibleInt,
    /// This field tracks the lenght of the `conditions` field. The point here
    /// is to be able to identify the conditions that need to be undone upon
    /// state restoration.
    conditions_sz: ReversibleInt,

    /// This field is merely used to track the constraints that have been
    /// scheduled for propagation
    scheduled: FxHashSet<Constraint>,
}
//------------------------------------------------------------------------------
// Obviously, we want a CpModelImpl to be an implementation of a CpModel
// even though it adds absolutely no behavior.
//------------------------------------------------------------------------------
impl<T: StateManager> CpModel for CpModelImpl<T> {}
//------------------------------------------------------------------------------
// Domain store facet
//------------------------------------------------------------------------------
impl<T: StateManager> DomainStore for CpModelImpl<T> {
    fn new_int_var(&mut self, min: isize, max: isize) -> Variable {
        self.domains.new_int_var(min, max)
    }

    fn new_bool_var(&mut self) -> Variable {
        self.domains.new_bool_var()
    }

    fn min(&self, var: Variable) -> Option<isize> {
        self.domains.min(var)
    }

    fn max(&self, var: Variable) -> Option<isize> {
        self.domains.max(var)
    }

    fn size(&self, var: Variable) -> usize {
        self.domains.size(var)
    }

    fn contains(&self, var: Variable, value: isize) -> bool {
        self.domains.contains(var, value)
    }

    fn fix(&mut self, var: Variable, value: isize) -> CPResult<()> {
        self.domains.fix(var, value)
    }

    fn remove(&mut self, var: Variable, value: isize) -> CPResult<()> {
        self.domains.remove(var, value)
    }

    fn remove_below(&mut self, var: Variable, value: isize) -> CPResult<()> {
        self.domains.remove_below(var, value)
    }

    fn remove_above(&mut self, var: Variable, value: isize) -> CPResult<()> {
        self.domains.remove_above(var, value)
    }
}
//------------------------------------------------------------------------------
// Save and Restore management
//------------------------------------------------------------------------------
impl<T: StateManager> SaveAndRestore for CpModelImpl<T> {
    fn save_state(&mut self) {
        self.domains.save_state()
    }

    fn restore_state(&mut self) {
        self.domains.restore_state();

        let prop_sz = self.prop_size();
        let cond_sz = self.cond_size();
        self.propagators.truncate(prop_sz);

        for (cond, prop) in self.conditions.iter().skip(cond_sz).copied() {
            if let Entry::Occupied(mut e) = self.listeners.entry(cond) {
                e.get_mut().remove(&prop);
                if e.get().is_empty() {
                    e.remove_entry();
                }
            }
        }
        self.conditions.truncate(cond_sz);
    }
}
//------------------------------------------------------------------------------
// Constraint store
//------------------------------------------------------------------------------
impl<T: StateManager> ConstraintStore for CpModelImpl<T> {
    fn install(&mut self, modeling_construct: &dyn ModelingConstruct) {
        modeling_construct.install(self)
    }

    fn post(&mut self, propagator: Box<dyn Propagator>) -> Constraint {
        self.propagators.push(propagator);
        Constraint(self.inc_prop_size() - 1)
    }

    fn propagate_on(&mut self, constraint: Constraint, cond: DomainCondition) {
        let mut must_push = false;
        match self.listeners.entry(cond) {
            Entry::Occupied(mut e) => {
                let v = e.get_mut();
                if !v.contains(&constraint) {
                    v.insert(constraint);
                    must_push = true;
                }
            }
            Entry::Vacant(e) => {
                let mut v = FxHashSet::default();
                v.insert(constraint);
                e.insert(v);
                must_push = true;
            }
        }

        if must_push {
            self.conditions.push((cond, constraint));
            self.inc_cond_size();
        }
    }

    fn fixpoint(&mut self) -> CPResult<()> {
        loop {
            self.schedule();
            let must_stop = self.scheduled.is_empty();
            if must_stop {
                return CPResult::Ok(());
            } else {
                let scheduled = &mut self.scheduled;
                let propagators = &mut self.propagators;
                let domains = &mut self.domains;

                for propagator in scheduled.drain() {
                    let propagator = propagators[propagator.0].as_mut();
                    propagator.propagate(domains)?;
                }
            }
        }
    }
}

impl<T: StateManager> From<T> for CpModelImpl<T> {
    fn from(mut sm: T) -> Self {
        let conditions_sz = sm.manage_int(0);
        let propagator_sz = sm.manage_int(0);
        Self {
            domains: DomainStoreImpl::from(sm),
            listeners: Default::default(),
            propagators: Default::default(),
            conditions: Default::default(),
            propagator_sz,
            conditions_sz,
            scheduled: Default::default(),
        }
    }
}
impl<T: StateManager + Default> Default for CpModelImpl<T> {
    fn default() -> Self {
        Self::from(T::default())
    }
}
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// ~~~ UTILITY METHODS ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
impl<T: StateManager> CpModelImpl<T> {
    /// Creates a new instance of the constraint store
    pub fn new(sm: T) -> Self {
        Self::from(sm)
    }
    /// Utility to reach the underlying state manager
    fn sm(&self) -> &T {
        self.domains.state_manager()
    }
    /// Utility to reach the underlying state manager in a mutable way
    fn sm_mut(&mut self) -> &mut T {
        self.domains.state_manager_mut()
    }
    /// returns the size of the propagators list
    fn prop_size(&self) -> usize {
        self.sm().get_int(self.propagator_sz) as usize
    }
    /// increments the size of the propagators list
    fn inc_prop_size(&mut self) -> usize {
        let var = self.propagator_sz;
        self.sm_mut().increment(var) as usize
    }
    /// returns the size of the conditions vector
    fn cond_size(&self) -> usize {
        self.sm().get_int(self.conditions_sz) as usize
    }
    /// increments the size of the conditions list
    fn inc_cond_size(&mut self) -> usize {
        let var = self.conditions_sz;
        self.sm_mut().increment(var) as usize
    }

    /// Schedules the execution of all the relevant propagators and clears the
    /// current set of events
    fn schedule(&mut self) {
        let schedule = &mut self.scheduled;
        let domains = &mut self.domains;
        let listeners = &self.listeners;

        domains.for_each_event(|e| {
            if e.is_fixed {
                let cond = DomainCondition::IsFixed(e.variable);
                Self::schedule_cond(cond, listeners, schedule);
            }
            if e.min_changed {
                let cond = DomainCondition::MinimumChanged(e.variable);
                Self::schedule_cond(cond, listeners, schedule);
            }
            if e.max_changed {
                let cond = DomainCondition::MaximumChanged(e.variable);
                Self::schedule_cond(cond, listeners, schedule);
            }
            if e.domain_changed {
                let cond = DomainCondition::DomainChanged(e.variable);
                Self::schedule_cond(cond, listeners, schedule);
            }
        });
        domains.clear_events();
    }
    /// Effectively schedule all propagators attached to a given condition
    fn schedule_cond(
        condition: DomainCondition,
        listeners: &FxHashMap<DomainCondition, FxHashSet<Constraint>>,
        sched: &mut FxHashSet<Constraint>,
    ) {
        if let Some(l) = listeners.get(&condition) {
            sched.extend(l.iter())
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ConstraintStore, DefaultCpModel, DomainCondition, DomainStore, Inconsistency,
        SaveAndRestore,
    };

    #[test]
    fn it_works() {
        let mut solver = DefaultCpModel::default();

        let x = solver.new_int_var(5, 10);
        let y = solver.new_bool_var();

        let cx = solver.post(Box::new(move |dom: &mut dyn DomainStore| {
            dom.fix_bool(y, true)
        }));

        let cy = solver.post(Box::new(move |dom: &mut dyn DomainStore| {
            if dom.min(x) >= Some(7) {
                dom.fix_bool(y, false)?;
                dom.fix(x, 7)?;
                Ok(())
            } else {
                Ok(())
            }
        }));

        solver.propagate_on(cx, DomainCondition::IsFixed(x));
        solver.propagate_on(cy, DomainCondition::DomainChanged(x));
        solver.save_state();

        assert_eq!(Ok(()), solver.remove_below(x, 6));
        assert_eq!(Ok(()), solver.fixpoint());
        solver.save_state();

        assert_eq!(Ok(()), solver.remove(x, 6));
        assert_eq!(Err(Inconsistency), solver.fixpoint());
        solver.restore_state();

        assert_eq!(5, solver.size(x));
        assert_eq!(2, solver.size(y));
    }
}
