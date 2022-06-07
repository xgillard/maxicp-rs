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

//! The state module comprises all traits and datastructures related to
//! the state (save and restore) management.
//!
//! # Note
//! The state manager have been thought of in terms of a visitor pattern. While
//! this might seem undesirable at first, this choice was operated for
//! * delivering the best possible performance at runtime
//! * getting over the absence of overloading in rust (which is good imho)
//! * maintaining the reversible objects themselves dead simple (which makes it
//!   easy to expose these objects to other languages -- ie python).
//!

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~ MANAGED RESOURCES ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// The identifier of a managed integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReversibleInt(usize);

/// The identifier of a managed boolean resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReversibleBool(ReversibleInt);

/// The identifier of a managed interval resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReversibleInterval(usize);

/// The identifier of a managed sparse set resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReversibleSparseSet(usize);

/// The identifier of a managed sparse set resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReversibleLazySparseSet(usize);

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~ MANAGER TRAITS ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// A state manager is an object capable of saving and restoring the state of
/// all types of managed resources.
pub trait StateManager:
    SaveAndRestore + IntManager + BoolManager + IntervalManager + SparseSetManager
{
}

/// An implementation of this type is capable of saving and restoring the
/// state of the resources it manages.
pub trait SaveAndRestore {
    /// Saves the current state of all managed resources
    fn save_state(&mut self);
    /// Restores the previous state of all managed resources
    fn restore_state(&mut self);
}

/// All the operations that can be made on an integer resource
pub trait IntManager {
    /// creates a new managed integer
    fn manage_int(&mut self, value: isize) -> ReversibleInt;
    /// returns the value of a managed integer
    fn get_int(&self, id: ReversibleInt) -> isize;
    /// sets a managed integer's value and returns the new value
    fn set_int(&mut self, id: ReversibleInt, value: isize) -> isize;
    /// increments a managed integer's value
    fn increment(&mut self, id: ReversibleInt) -> isize;
    /// decrements a managed integer's value
    fn decrement(&mut self, id: ReversibleInt) -> isize;
}

/// All the operations that can be made on a boolean resource
pub trait BoolManager {
    /// creates a new managed boolean
    fn manage_bool(&mut self, v: bool) -> ReversibleBool;
    /// returns the value of a managed boolean
    fn get_bool(&self, id: ReversibleBool) -> bool;
    /// sets a managed boolean's value and returns the new value
    fn set_bool(&mut self, id: ReversibleBool, value: bool) -> bool;
    /// flips a boolean's value and returns it
    fn flip_bool(&mut self, id: ReversibleBool) -> bool {
        self.set_bool(id, self.get_bool(id).not())
    }
}

/// All the operations that can be applied to an interval
pub trait IntervalManager {
    /// creates a new managed interval low..=high (that is, an interval where
    /// both ends are included in the interval)
    ///
    /// # Parameters
    /// - low: the lowest possible value in this interval (included)
    /// - high: the highest possible value in this interval (included)
    fn manage_interval(&mut self, low: isize, high: isize) -> ReversibleInterval;
    /// Returns true iff the interval is empty
    fn interval_is_empty(&self, id: ReversibleInterval) -> bool;
    /// Returns the number of integer values in the interval
    fn interval_size(&self, id: ReversibleInterval) -> usize;
    /// Returns the minimum integer value in the interval (if there is one)
    fn interval_get_min(&self, id: ReversibleInterval) -> Option<isize>;
    /// Returns the maximum integer value in the interval (if there is one)
    fn interval_get_max(&self, id: ReversibleInterval) -> Option<isize>;
    /// Returns true iff the given interval comprises the specified value
    fn interval_contains(&self, id: ReversibleInterval, value: isize) -> bool;
    /// removes all values in the interval except the given value (if it belongs to the set)
    fn interval_remove_all_but(&mut self, id: ReversibleInterval, value: isize);
    /// removes all values in the interval
    fn interval_remove_all(&mut self, id: ReversibleInterval);
    /// remove from the set all the items having a value lower than the given `value`
    fn interval_remove_below(&mut self, id: ReversibleInterval, value: isize);
    /// remove from the set all the items having a value greater than the given `value`
    fn interval_remove_above(&mut self, id: ReversibleInterval, value: isize);
    /// Calls the function f once for each value in the interval
    /// identified with 'id'
    fn interval_for_each<F: FnMut(isize)>(&self, id: ReversibleInterval, f: F);
}

/// All the operations that can be applied to a sparse set
pub trait SparseSetManager {
    /// creates a new managed sparse set with values
    /// [0 + value_offset, 1 + value_offset, 2 + value_offset, ... , n-1 + value_offset]
    ///
    /// # Params
    /// - n: the number of values in the sparse set
    /// - val_offset: the "offset" of the first value that belongs to the set
    fn manage_sparse_set(&mut self, n: usize, val_offset: isize) -> ReversibleSparseSet;
    /// returns the size of the given sparse set
    fn sparse_set_size(&self, id: ReversibleSparseSet) -> usize;
    /// returns true iff the sparse set is empty
    fn sparse_set_is_empty(&self, id: ReversibleSparseSet) -> bool;
    /// returns the minimum value of the sparse set (if it exists)
    fn sparse_set_get_min(&self, id: ReversibleSparseSet) -> Option<isize>;
    /// returns the maximum value of the sparse set (if it exists)
    fn sparse_set_get_max(&self, id: ReversibleSparseSet) -> Option<isize>;
    /// returns true iff the sparse set contains the designated value
    fn sparse_set_contains(&self, id: ReversibleSparseSet, value: isize) -> bool;
    /// removes the given value from the sparse set and returns a boolean telling
    /// whether or not the value was actually deleted from the set
    fn sparse_set_remove(&mut self, id: ReversibleSparseSet, value: isize) -> bool;
    /// removes all values in the set
    fn sparse_set_remove_all(&mut self, id: ReversibleSparseSet);
    /// removes all values in the set except the given value (if it belongs to the set)
    fn sparse_set_remove_all_but(&mut self, id: ReversibleSparseSet, value: isize);
    /// remove from the set all the items having a value lower than the given `value`
    fn sparse_set_remove_below(&mut self, id: ReversibleSparseSet, val: isize);
    /// remove from the set all the items having a value higher than the given `value`
    fn sparse_set_remove_above(&mut self, id: ReversibleSparseSet, val: isize);
    /// Calls the function f once for each value in the reversible sparse set
    /// identified with 'id'
    fn sparse_set_for_each<F: FnMut(isize)>(&self, id: ReversibleSparseSet, f: F);
}

/// The state manager is in charge of storing and restoring the data from
/// and to the trail
mod trailed;
use std::ops::Not;

pub use trailed::*;
