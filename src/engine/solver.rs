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

use super::{DomainStore, CPResult};

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

/// A domain listener is conceptually very close to a propagator: it is a small
/// portion of code that can be activated depending on the occurrence of some
/// condition on the domain of a variable. When that code is executed, it is
/// typically used to either *log* the occurence of an event, or to post new
/// constraints to reinforce the propagation in the current subtree. 
/// 
/// A domain listener is semantically different though: it it not meant to 
/// propagate information (remove values from the domain of variables) on its
/// own.
pub trait DomainListener {
    /// Actually runs the custom propagation algorithm
    fn on_change(&mut self, domain_store: &mut dyn DomainStore) -> CPResult<()>;
}

/// Any closure/function that accepts a mutable ref to the domain store can be 
/// a propagator.
impl <F: FnMut(&mut dyn DomainStore) -> CPResult<()>> Propagator for F {
    fn propagate(&mut self, domain_store: &mut dyn DomainStore) -> CPResult<()> {
        self(domain_store)
    }
}
/// Any closure/function that accepts a mutable ref to the domain store can be 
/// a domain listener.
impl <F: FnMut(&mut dyn DomainStore) -> CPResult<()>> DomainListener for F {
    fn on_change(&mut self, domain_store: &mut dyn DomainStore) -> CPResult<()> {
        self(domain_store)
    }
}