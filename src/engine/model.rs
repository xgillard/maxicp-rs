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
    /// Schedules the execution of a given constraint (propagator)
    fn schedule(&mut self, constraint: Constraint);
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
        self.scheduled.clear();
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

    fn schedule(&mut self, constraint: Constraint) {
        self.scheduled.insert(constraint);
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
            self.schedule_relevant();
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
    fn from(sm: T) -> Self {
        Self::new(sm)
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
    pub fn new(mut sm: T) -> Self {
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
    fn schedule_relevant(&mut self) {
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

// #############################################################################
// ### UNIT TESTS ##############################################################
// #############################################################################

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~ QUICK CHECK THAT IT WORKS ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#[cfg(test)]
mod test_default_model_quickcheck {
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

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~ DOMAINSTORE ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// The implementation of the domainstore trait by the cpmodelimpl is delegated
// to the `domains` field of that struct. As annoying as it is, this test suite
// is largely copy-pasted from the test suite of domainstoreimpl because, in
// the end, it tests the same behavior. It does however not test any behavior
// related to the occurence of domain events since these are dealt with by the
// domainbroker responsibility of the domainstoreimpl.
#[cfg(test)]
mod test_default_model_domainstore {
    use crate::{DefaultCpModel, DomainStore, Inconsistency, SaveAndRestore};

    #[test]
    fn min_yields_the_minimum_of_domain() {
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Some(5), ds.min(x));
        assert_eq!(Some(0), ds.min(y));
        assert_eq!(Some(0), ds.min(z));
    }
    #[test]
    fn min_yields_the_minimum_of_domain_after_update() {
        let mut ds = DefaultCpModel::default();
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
        let mut ds = DefaultCpModel::default();
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
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Some(10), ds.max(x));
        assert_eq!(Some(5), ds.max(y));
        assert_eq!(Some(1), ds.max(z));
    }
    #[test]
    fn max_yields_the_maximum_of_domain_after_update() {
        let mut ds = DefaultCpModel::default();
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
        let mut ds = DefaultCpModel::default();
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
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(6, ds.size(x));
        assert_eq!(6, ds.size(y));
        assert_eq!(2, ds.size(z));
    }
    #[test]
    fn size_yields_the_domain_size_with_hole() {
        let mut ds = DefaultCpModel::default();
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
        let mut ds = DefaultCpModel::default();
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
        let mut ds = DefaultCpModel::default();
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
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert!(!ds.contains(x, -5));
        assert!(!ds.contains(y, -5));
        assert!(!ds.contains(z, -5));
    }
    #[test]
    fn contains_returns_true_for_lb() {
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert!(ds.contains(x, 5));
        assert!(ds.contains(y, 0));
        assert!(ds.contains(z, 0));
    }
    #[test]
    fn contains_returns_false_for_value_gt_than_ub() {
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert!(!ds.contains(x, 45));
        assert!(!ds.contains(y, 45));
        assert!(!ds.contains(z, 45));
    }
    #[test]
    fn contains_returns_true_for_ub() {
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert!(ds.contains(x, 10));
        assert!(ds.contains(y, 5));
        assert!(ds.contains(z, 1));
    }
    #[test]
    fn contains_returns_false_for_hole() {
        let mut ds = DefaultCpModel::default();
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
        let mut ds = DefaultCpModel::default();
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
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Err(Inconsistency), ds.fix(x, -10));
        assert_eq!(Err(Inconsistency), ds.fix(y, -10));
        assert_eq!(Err(Inconsistency), ds.fix(z, -10));
    }
    #[test]
    fn fix_fails_when_higher_than_ub() {
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Err(Inconsistency), ds.fix(x, 20));
        assert_eq!(Err(Inconsistency), ds.fix(y, 20));
        assert_eq!(Err(Inconsistency), ds.fix(z, 20));
    }
    #[test]
    fn fix_fails_when_hole() {
        let mut ds = DefaultCpModel::default();
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
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.fix(x, 7));
        assert_eq!(Ok(()), ds.fix(y, 3));
        assert_eq!(Ok(()), ds.fix(z, 0));
    }

    #[test]
    fn remove_has_no_effect_when_out_of_domain() {
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove(x, -10));
        assert_eq!(Ok(()), ds.remove(y, -10));
        assert_eq!(Ok(()), ds.remove(z, -10));
    }

    #[test]
    fn remove_fails_when_it_makes_domain_empty() {
        let mut ds = DefaultCpModel::default();
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
    }
    #[test]
    fn remove_punches_a_hole_when_in_the_middle() {
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove(x, 7));
        assert_eq!(Ok(()), ds.remove(y, 3));
        assert_eq!(Ok(()), ds.remove(z, 0));
    }

    #[test]
    fn remove_may_adapt_minimum() {
        let mut ds = DefaultCpModel::default();
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
    }

    #[test]
    fn remove_may_adapt_maximum() {
        let mut ds = DefaultCpModel::default();
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
    }

    #[test]
    fn remove_above_has_no_effect_when_out_of_domain() {
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove_above(x, 20));
        assert_eq!(Ok(()), ds.remove_above(y, 20));
        assert_eq!(Ok(()), ds.remove_above(z, 20));
    }

    #[test]
    fn remove_above_fails_when_it_makes_domain_empty() {
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Err(Inconsistency), ds.remove_above(x, -10));
        assert_eq!(Err(Inconsistency), ds.remove_above(y, -10));
        assert_eq!(Err(Inconsistency), ds.remove_above(z, -10));
    }

    #[test]
    fn remove_above_may_adapt_maximum() {
        let mut ds = DefaultCpModel::default();
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
    }

    #[test]
    fn remove_below_has_no_effect_when_out_of_domain() {
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Ok(()), ds.remove_below(x, -20));
        assert_eq!(Ok(()), ds.remove_below(y, -20));
        assert_eq!(Ok(()), ds.remove_below(z, -20));
    }

    #[test]
    fn remove_below_fails_when_it_makes_domain_empty() {
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(0, 5);
        let z = ds.new_bool_var();

        assert_eq!(Err(Inconsistency), ds.remove_below(x, 20));
        assert_eq!(Err(Inconsistency), ds.remove_below(y, 20));
        assert_eq!(Err(Inconsistency), ds.remove_below(z, 20));
    }

    #[test]
    fn remove_below_may_adapt_minimum() {
        let mut ds = DefaultCpModel::default();
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
    }

    #[test]
    fn is_fixed_only_when_one_value_left() {
        let mut ds = DefaultCpModel::default();
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
        let mut ds = DefaultCpModel::default();
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
        let mut ds = DefaultCpModel::default();
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

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~ SAVE AND RESTORE ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// A large fraction of the save and restore behavior is delegated to the
// `domains` field of the cpmodelimpl. However, the model **does** add some
// behavior and acts as a decorator to the domainstoreimpl. This test suite
// largely copies the one from domainstoreimpl and adds some additional checks
// that are specific to the **decorations** added by the cpmodelimpl.
#[cfg(test)]
mod test_default_model_saveandstore {
    use crate::Inconsistency;

    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn save_and_restore_state_should_work_together() {
        let mut ds = DefaultCpModel::default();
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

    /*
    Unfortunately, these are best tested together (long-ish test)
    - restore drops all stale propagators
    - a stale propagator is never fired after having been dropped on restore
    - restore detaches all stale propagators
    - restore drops all stale conditions
    */
    #[test]
    fn restore_drops_all_stale_propagators_and_conditions() {
        let mut ds = DefaultCpModel::default();
        let x = ds.new_int_var(5, 10);
        let y = ds.new_int_var(5, 10);
        let z = ds.new_int_var(5, 10);

        let flag_x = Rc::new(RefCell::new(false));
        let flag_y = Rc::new(RefCell::new(false));
        let flag_z = Rc::new(RefCell::new(false));

        // constraint x is created and installed at root level. it is never
        // removed, and it is fired every time the domain of variable x is
        // changed.
        let rc_flag_x = flag_x.clone();
        let constraint_x = ds.post(Box::new(move |_: &mut dyn DomainStore| {
            *rc_flag_x.borrow_mut() = true;
            Ok(())
        }));
        ds.propagate_on(constraint_x, DomainCondition::DomainChanged(x));
        ds.save_state();

        // checks
        assert_eq!(1, ds.prop_size());
        assert_eq!(1, ds.cond_size());
        assert_eq!(1, ds.propagators.len());
        assert_eq!(1, ds.conditions.len());
        //
        assert_eq!(Ok(()), ds.remove(x, 5));
        assert_eq!(Ok(()), ds.remove(y, 5));
        assert_eq!(Ok(()), ds.remove(z, 5));
        assert_eq!(Ok(()), ds.fixpoint());
        assert!(*flag_x.borrow()); // x was triggered
        assert!(!*flag_y.borrow()); // y was not
        assert!(!*flag_z.borrow()); // z was not
        *flag_x.borrow_mut() = false;
        //

        // constraint y is created at first level but not installed untill
        // level 2. reverting back to level 1 from level 2 must not drop the
        // propagator but it should make it stop reacting to changes in the
        // domain of y
        let rc_flag_y = flag_y.clone();
        let constraint_y = ds.post(Box::new(move |_: &mut dyn DomainStore| {
            *rc_flag_y.borrow_mut() = true;
            Ok(())
        }));
        ds.save_state();

        // checks
        assert_eq!(2, ds.prop_size());
        assert_eq!(1, ds.cond_size());
        assert_eq!(2, ds.propagators.len());
        assert_eq!(1, ds.conditions.len());

        //
        assert_eq!(Ok(()), ds.remove(x, 6));
        assert_eq!(Ok(()), ds.remove(y, 6));
        assert_eq!(Ok(()), ds.remove(z, 6));
        assert_eq!(Ok(()), ds.fixpoint());
        assert!(*flag_x.borrow()); // x was triggered
        assert!(!*flag_y.borrow()); // y was not
        assert!(!*flag_z.borrow()); // z was not
        *flag_x.borrow_mut() = false;
        //

        // activate constraint_y
        ds.propagate_on(constraint_y, DomainCondition::DomainChanged(y));

        // constraint z is created and installed at level 2. it must be deleted
        // completely upon restoration
        let rc_flag_z = flag_z.clone();
        let constraint_z = ds.post(Box::new(move |_: &mut dyn DomainStore| {
            *rc_flag_z.borrow_mut() = true;
            Ok(())
        }));
        ds.propagate_on(constraint_z, DomainCondition::IsFixed(z));
        ds.save_state();

        ds.propagate_on(constraint_z, DomainCondition::DomainChanged(z));
        // We are at level 3 here
        // checks
        assert_eq!(3, ds.prop_size());
        assert_eq!(4, ds.cond_size());
        assert_eq!(3, ds.propagators.len());
        assert_eq!(4, ds.conditions.len());
        //
        assert_eq!(Ok(()), ds.remove(x, 7));
        assert_eq!(Ok(()), ds.remove(y, 7));
        assert_eq!(Ok(()), ds.remove(z, 7));
        assert_eq!(Ok(()), ds.fixpoint());
        assert!(*flag_x.borrow()); // x was triggered
        assert!(*flag_y.borrow()); // y was not
        assert!(*flag_z.borrow()); // z was not
        *flag_x.borrow_mut() = false;
        *flag_y.borrow_mut() = false;
        *flag_z.borrow_mut() = false;
        //

        ds.restore_state();
        // We are at level 2 -> domain changed no longer attached to z
        assert_eq!(3, ds.prop_size());
        assert_eq!(3, ds.cond_size());
        assert_eq!(3, ds.propagators.len());
        assert_eq!(3, ds.conditions.len());
        //
        assert_eq!(Ok(()), ds.remove(x, 8));
        assert_eq!(Ok(()), ds.remove(y, 8));
        assert_eq!(Ok(()), ds.remove(z, 8));
        assert_eq!(Ok(()), ds.fixpoint());
        assert!(*flag_x.borrow()); // x was triggered
        assert!(*flag_y.borrow()); // y was not
        assert!(!*flag_z.borrow()); // z was not
        *flag_x.borrow_mut() = false;
        *flag_y.borrow_mut() = false;
        *flag_z.borrow_mut() = false;

        // We are at level 2 -> fixed event still attached to z
        assert_eq!(Ok(()), ds.remove(x, 7));
        assert_eq!(Ok(()), ds.remove(y, 7));
        assert_eq!(Ok(()), ds.fix(z, 7));
        assert_eq!(Ok(()), ds.fixpoint());
        assert!(*flag_x.borrow()); // x was triggered
        assert!(*flag_y.borrow()); // y was not
        assert!(*flag_z.borrow()); // z was not
        *flag_x.borrow_mut() = false;
        *flag_y.borrow_mut() = false;
        *flag_z.borrow_mut() = false;

        // Level 1: there are two propagators left but only one is active
        ds.restore_state();
        // checks
        assert_eq!(2, ds.prop_size());
        assert_eq!(1, ds.cond_size());
        assert_eq!(2, ds.propagators.len());
        assert_eq!(1, ds.conditions.len());
        //
        assert_eq!(Ok(()), ds.remove(x, 7));
        assert_eq!(Ok(()), ds.remove(y, 7));
        assert_eq!(Ok(()), ds.remove(z, 7));
        assert_eq!(Ok(()), ds.fixpoint());
        assert!(*flag_x.borrow()); // x was triggered
        assert!(!*flag_y.borrow()); // y was not
        assert!(!*flag_z.borrow()); // z was not
        *flag_x.borrow_mut() = false;
        *flag_y.borrow_mut() = false;
        *flag_z.borrow_mut() = false;
        //

        // Level 0: there only one propagator left
        ds.restore_state();
        // checks
        assert_eq!(1, ds.prop_size());
        assert_eq!(1, ds.cond_size());
        assert_eq!(1, ds.propagators.len());
        assert_eq!(1, ds.conditions.len());
        //
        assert_eq!(Ok(()), ds.remove(x, 7));
        assert_eq!(Ok(()), ds.remove(y, 7));
        assert_eq!(Ok(()), ds.remove(z, 7));
        assert_eq!(Ok(()), ds.fixpoint());
        assert!(*flag_x.borrow()); // x was triggered
        assert!(!*flag_y.borrow()); // y was not
        assert!(!*flag_z.borrow()); // z was not
        *flag_x.borrow_mut() = false;
        *flag_y.borrow_mut() = false;
        *flag_z.borrow_mut() = false;
        //
    }

    #[test]
    fn restore_unschedules_all_scheduled_propagators() {
        let mut model = DefaultCpModel::default();
        let c = model.post(Box::new(move |_: &mut dyn DomainStore| Err(Inconsistency)));
        model.save_state();
        model.schedule(c);
        model.restore_state();
        assert_eq!(Ok(()), model.fixpoint());
    }
}

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~ CONSTRAINTSTORE ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#[cfg(test)]
mod test_default_model_constraintstore {
    use crate::Inconsistency;

    use super::*;
    use std::cell::RefCell;

    struct MockConstruct {
        installed: RefCell<bool>,
    }
    impl MockConstruct {
        fn new() -> Self {
            Self {
                installed: RefCell::new(false),
            }
        }
    }
    impl ModelingConstruct for MockConstruct {
        fn install(&self, _cstore: &mut dyn crate::ConstraintStore) {
            *self.installed.borrow_mut() = true;
        }
    }
    #[test]
    fn install_simply_delegates_to_model_construct() {
        let mut model = DefaultCpModel::default();
        let construct = MockConstruct::new();

        model.install(&construct);
        assert!(*construct.installed.borrow());
    }
    #[test]
    fn post_adds_a_propagator_but_does_not_attach_it() {
        let mut model = DefaultCpModel::default();
        let x = model.new_int_var(0, 9);
        assert_eq!(0, model.prop_size());
        assert_eq!(0, model.cond_size());

        model.post(Box::new(move |_: &mut dyn DomainStore| Err(Inconsistency)));

        assert_eq!(1, model.prop_size());
        assert_eq!(0, model.cond_size());

        assert_eq!(Ok(()), model.remove(x, 5));
        assert_eq!(Ok(()), model.fixpoint());
    }
    #[test]
    fn schedule_prepares_constraint_for_execution() {
        let mut model = DefaultCpModel::default();
        let x = model.new_int_var(0, 9);

        let c = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.fix(x, 7)));

        // not scheduled yet, fixpoint wont change domain
        assert_eq!(Ok(()), model.fixpoint());
        assert_eq!(10, model.size(x));
        assert_eq!(Some(0), model.min(x));
        assert_eq!(Some(9), model.max(x));

        // now let us schedule the propagator and the fixpoint will set x to 7
        model.schedule(c);
        assert_eq!(Ok(()), model.fixpoint());
        assert_eq!(1, model.size(x));
        assert_eq!(Some(7), model.min(x));
        assert_eq!(Some(7), model.max(x));
    }

    #[test]
    fn propagate_on_does_not_insert_duplicate() {
        let mut model = DefaultCpModel::default();
        let x = model.new_int_var(0, 9);
        let c = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.fix(x, 7)));

        model.propagate_on(c, DomainCondition::IsFixed(x));
        assert_eq!(1, model.cond_size());

        model.propagate_on(c, DomainCondition::IsFixed(x));
        model.propagate_on(c, DomainCondition::IsFixed(x));
        assert_eq!(1, model.cond_size());

        model.save_state();
        model.propagate_on(c, DomainCondition::DomainChanged(x));
        assert_eq!(2, model.cond_size());

        model.propagate_on(c, DomainCondition::DomainChanged(x));
        model.propagate_on(c, DomainCondition::DomainChanged(x));
        assert_eq!(2, model.cond_size());

        model.save_state();
        model.propagate_on(c, DomainCondition::MaximumChanged(x));
        assert_eq!(3, model.cond_size());

        model.propagate_on(c, DomainCondition::MaximumChanged(x));
        model.propagate_on(c, DomainCondition::MaximumChanged(x));
        assert_eq!(3, model.cond_size());

        model.save_state();
        model.propagate_on(c, DomainCondition::MinimumChanged(x));
        assert_eq!(4, model.cond_size());

        model.propagate_on(c, DomainCondition::MinimumChanged(x));
        model.propagate_on(c, DomainCondition::MinimumChanged(x));
        assert_eq!(4, model.cond_size());
    }
    #[test]
    fn different_constraints_listening_on_the_same_event_is_not_a_duplicate() {
        let mut model = DefaultCpModel::default();
        let x = model.new_int_var(0, 9);
        let c = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.fix(x, 7)));
        let d = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.fix(x, 7)));

        model.propagate_on(c, DomainCondition::IsFixed(x));
        model.propagate_on(d, DomainCondition::IsFixed(x));
        assert_eq!(2, model.cond_size());
    }
    #[test]
    fn propagate_on_fixed_does_nothing_as_it_is_not_fixed() {
        let mut model = DefaultCpModel::default();
        let x = model.new_int_var(0, 9);

        let c = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.fix(x, 7)));
        model.propagate_on(c, DomainCondition::IsFixed(x));

        // not scheduled yet, fixpoint wont change domain
        assert_eq!(Ok(()), model.fixpoint());
        assert_eq!(10, model.size(x));
        assert_eq!(Some(0), model.min(x));
        assert_eq!(Some(9), model.max(x));

        assert_eq!(Ok(()), model.remove(x, 5));
        assert_eq!(Ok(()), model.fixpoint());
        assert_eq!(9, model.size(x));
        assert_eq!(Some(0), model.min(x));
        assert_eq!(Some(9), model.max(x));
    }
    #[test]
    fn propagate_on_fixed_propagates_when_var_is_fixed() {
        let mut model = DefaultCpModel::default();
        let x = model.new_int_var(0, 9);

        let c = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.fix(x, 7)));
        model.propagate_on(c, DomainCondition::IsFixed(x));
        assert_eq!(Ok(()), model.fix(x, 5));
        assert_eq!(Err(Inconsistency), model.fixpoint());
    }

    #[test]
    fn propagate_on_min_change_does_nothing_unless_minimum_changes() {
        let mut model = DefaultCpModel::default();
        let x = model.new_int_var(0, 9);

        let c = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.fix(x, 7)));
        model.propagate_on(c, DomainCondition::MinimumChanged(x));

        // not scheduled yet, fixpoint wont change domain
        assert_eq!(Ok(()), model.fixpoint());
        assert_eq!(10, model.size(x));
        assert_eq!(Some(0), model.min(x));
        assert_eq!(Some(9), model.max(x));

        // minimum has not changed, it does not execute
        assert_eq!(Ok(()), model.remove_above(x, 7));
        assert_eq!(Ok(()), model.fixpoint());
        assert_eq!(8, model.size(x));
        assert_eq!(Some(0), model.min(x));
        assert_eq!(Some(7), model.max(x));

        // minimum has changed, it does execute
        assert_eq!(Ok(()), model.remove_below(x, 3));
        assert_eq!(Ok(()), model.fixpoint());
        assert_eq!(1, model.size(x));
        assert_eq!(Some(7), model.min(x));
        assert_eq!(Some(7), model.max(x));
    }
    #[test]
    fn propagate_on_max_change_does_nothing_unless_maximum_changes() {
        let mut model = DefaultCpModel::default();
        let x = model.new_int_var(0, 9);

        let c = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.fix(x, 7)));
        model.propagate_on(c, DomainCondition::MaximumChanged(x));

        // not scheduled yet, fixpoint wont change domain
        assert_eq!(Ok(()), model.fixpoint());
        assert_eq!(10, model.size(x));
        assert_eq!(Some(0), model.min(x));
        assert_eq!(Some(9), model.max(x));

        // minimum has not changed, it does not execute
        assert_eq!(Ok(()), model.remove_below(x, 3));
        assert_eq!(Ok(()), model.fixpoint());
        assert_eq!(7, model.size(x));
        assert_eq!(Some(3), model.min(x));
        assert_eq!(Some(9), model.max(x));

        // minimum has changed, it does execute
        assert_eq!(Ok(()), model.remove_above(x, 8));
        assert_eq!(Ok(()), model.fixpoint());
        assert_eq!(1, model.size(x));
        assert_eq!(Some(7), model.min(x));
        assert_eq!(Some(7), model.max(x));
    }
    #[test]
    fn propagate_on_change_reacts_on_every_change() {
        let mut model = DefaultCpModel::default();
        let x = model.new_int_var(0, 9);

        let c = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.fix(x, 7)));
        model.propagate_on(c, DomainCondition::DomainChanged(x));

        // not scheduled yet, fixpoint wont change domain
        assert_eq!(Ok(()), model.fixpoint());
        assert_eq!(10, model.size(x));
        assert_eq!(Some(0), model.min(x));
        assert_eq!(Some(9), model.max(x));

        // minimum has not changed, it does not execute
        assert_eq!(Ok(()), model.remove(x, 3));
        assert_eq!(Ok(()), model.fixpoint());
        assert_eq!(1, model.size(x));
        assert_eq!(Some(7), model.min(x));
        assert_eq!(Some(7), model.max(x));
    }

    #[test]
    fn fixpoint_runs_propagators_until_it_reaches_fixpoint() {
        let mut model = DefaultCpModel::default();
        let x = model.new_int_var(0, 9);
        let y = model.new_int_var(0, 9);
        let z = model.new_int_var(0, 9);

        let boot = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.remove(x, 5)));
        model.schedule(boot);

        let cx = model.post(Box::new(move |dom: &mut dyn DomainStore| {
            dom.remove_above(y, 7)
        }));
        model.propagate_on(cx, DomainCondition::DomainChanged(x));

        let cy1 = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.fix(y, 3)));
        model.propagate_on(cy1, DomainCondition::MaximumChanged(y));

        let cy2 = model.post(Box::new(move |dom: &mut dyn DomainStore| {
            dom.remove_below(z, dom.min(y).unwrap())
        }));
        model.propagate_on(cy2, DomainCondition::IsFixed(y));

        let cz = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.fix(z, 3)));
        model.propagate_on(cz, DomainCondition::MinimumChanged(z));

        assert_eq!(10, model.size(x));
        assert_eq!(10, model.size(y));
        assert_eq!(10, model.size(z));

        assert_eq!(Ok(()), model.fixpoint());
        assert_eq!(9, model.size(x));
        assert_eq!(1, model.size(y));
        assert_eq!(1, model.size(z));
        //
        assert_eq!(Some(0), model.min(x));
        assert_eq!(Some(9), model.max(x));
        assert_eq!(Some(3), model.min(y));
        assert_eq!(Some(3), model.max(y));
        assert_eq!(Some(3), model.min(z));
        assert_eq!(Some(3), model.max(z));
    }

    #[test]
    fn fixpoint_stops_running_upon_inconsistency() {
        let mut model = DefaultCpModel::default();
        let x = model.new_int_var(0, 9);
        let y = model.new_int_var(0, 9);
        let z = model.new_int_var(0, 9);

        let boot = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.remove(x, 5)));
        model.schedule(boot);

        let cx = model.post(Box::new(move |_: &mut dyn DomainStore| Err(Inconsistency)));
        model.propagate_on(cx, DomainCondition::DomainChanged(x));

        let cy1 = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.fix(y, 3)));
        model.propagate_on(cy1, DomainCondition::MaximumChanged(y));

        let cy2 = model.post(Box::new(move |dom: &mut dyn DomainStore| {
            dom.remove_below(z, dom.min(y).unwrap())
        }));
        model.propagate_on(cy2, DomainCondition::IsFixed(y));

        let cz = model.post(Box::new(move |dom: &mut dyn DomainStore| dom.fix(z, 3)));
        model.propagate_on(cz, DomainCondition::MinimumChanged(z));

        assert_eq!(10, model.size(x));
        assert_eq!(10, model.size(y));
        assert_eq!(10, model.size(z));

        assert_eq!(Err(Inconsistency), model.fixpoint());
        assert_eq!(9, model.size(x));
        assert_eq!(10, model.size(y));
        assert_eq!(10, model.size(z));
        //
        assert_eq!(Some(0), model.min(x));
        assert_eq!(Some(9), model.max(x));
        assert_eq!(Some(0), model.min(y));
        assert_eq!(Some(9), model.max(y));
        assert_eq!(Some(0), model.min(z));
        assert_eq!(Some(9), model.max(z));
    }
}
