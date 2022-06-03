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

//! This module defines the data structures and utilities that are used to
//! save and restore data from the solver trail.

use std::ops::Not;

use crate::utils::Int;

/// The identifier of managed boolean resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReversibleBool(Reversible);

/// The identifier of managed integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReversibleInt(Reversible);

/// The identifier of managed integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReversibleSparseSet(usize);

/// A richer structure that represents the non primitive things that are tracked
/// by a simple manager
#[derive(Debug, Clone, Copy, Default)]
struct RichLayer {
    /// how many sparse sets have already been recorded ?
    sparse_sets: usize,
    /// length of the sparse sets data
    sparse_set_data: usize,
}

/// A simple state manager that can manage booleans, integers, sparse sets
#[derive(Debug, Clone)]
pub struct SimpleManager {
    /// A "low level" state manager which is used to deal with the "primitive"
    /// data types
    delegate: StateManager<isize>,

    /// Holds the metadata about sparse sets
    sparse_sets: Vec<SparseSet>,
    /// Holds the actual content of the sparse sets
    sparse_set_data: Vec<usize>,
    /// Holds the indices of the data in a sparse set
    sparse_set_idx: Vec<usize>,

    /// Some additional bookkeeping data to keep track of the richer structures
    /// that have been built on top of the raw state manager
    layers: Vec<RichLayer>,
}
impl Default for SimpleManager {
    fn default() -> Self {
        Self::new()
    }
}
impl SimpleManager {
    /// Creates a new SimpleManager
    pub fn new() -> Self {
        Self {
            delegate: StateManager::new(),

            sparse_sets: vec![],
            sparse_set_data: vec![],
            sparse_set_idx: vec![],

            layers: vec![RichLayer {
                sparse_sets: 0,
                sparse_set_data: 0,
            }],
        }
    }
    /// Saves the current state
    pub fn push(&mut self) {
        self.delegate.push();

        // additional book keeping
        self.layers.push(RichLayer {
            sparse_sets: self.sparse_sets.len(),
            sparse_set_data: self.sparse_set_data.len(),
        })
    }
    /// Restores the previous state
    pub fn pop(&mut self) {
        self.delegate.pop();

        // additional book keeping
        let layer = self.layers.pop().expect("cannot pop above the first push");
        self.sparse_sets.truncate(layer.sparse_sets);
        self.sparse_set_data.truncate(layer.sparse_set_data);
    }
}
//------------------------------------------------------------------------------
// Bool management
//------------------------------------------------------------------------------
impl SimpleManager {
    /// creates a new managed boolean
    pub fn manage_bool(&mut self, v: bool) -> ReversibleBool {
        ReversibleBool(self.delegate.manage(v as isize))
    }
    /// returns the value of a managed boolean
    pub fn get_bool(&self, id: ReversibleBool) -> bool {
        self.delegate.get_value(id.0) != 0
    }
    /// sets a managed boolean's value and returns the new value
    pub fn set_bool(&mut self, id: ReversibleBool, value: bool) -> bool {
        self.delegate.set_value(id.0, value as isize) != 0
    }
    /// flips a boolean's value and returns it
    pub fn flip_bool(&mut self, id: ReversibleBool) -> bool {
        self.delegate
            .set_value(id.0, self.delegate.get_value(id.0).not())
            != 0
    }
}
//------------------------------------------------------------------------------
// Int management
//------------------------------------------------------------------------------
impl SimpleManager {
    /// creates a new managed integer
    pub fn manage_int(&mut self, v: isize) -> ReversibleInt {
        ReversibleInt(self.delegate.manage(v))
    }
    /// returns the value of a managed integer
    pub fn get_int(&self, id: ReversibleInt) -> isize {
        self.delegate.get_value(id.0)
    }
    /// sets a managed integer's value and returns the new value
    pub fn set_int(&mut self, id: ReversibleInt, value: isize) -> isize {
        self.delegate.set_value(id.0, value)
    }
    /// increments a managed integer's value
    pub fn increment(&mut self, id: ReversibleInt) -> isize {
        self.delegate.increment(id.0)
    }
    /// decrements a managed integer's value
    pub fn decrement(&mut self, id: ReversibleInt) -> isize {
        self.delegate.decrement(id.0)
    }
}
//------------------------------------------------------------------------------
// Sparse sets management
//------------------------------------------------------------------------------

/// The information that needs to be maintained in order to deal with a
/// sparse set
#[derive(Debug, Clone, Copy)]
struct SparseSet {
    /// offset of the values
    val_offset: isize,
    /// start index of the sparse set (included)
    start: usize,
    /// capcity of the sparse set
    capa: usize,
    /// the current size of the sparse set
    size: ReversibleInt,
    /// the minimum value in the set
    min: ReversibleInt,
    /// the maximum value in the set
    max: ReversibleInt,
}
impl SimpleManager {
    /// creates a new managed sparse set with values
    /// [0 + value_offset, 1 + value_offset, 2 + value_offset, ... , n-1 + value_offset]
    ///
    /// # Params
    /// - n: the number of values in the sparse set
    /// - val_offset: the "offset" of the first value that belongs to the set
    pub fn manage_sparse_set(&mut self, n: usize, val_offset: isize) -> ReversibleSparseSet {
        let id = self.sparse_sets.len();
        let data_len = self.sparse_set_data.len();

        let start = data_len;
        let capa = n;

        for i in 0..n {
            self.sparse_set_data.push(i);
            self.sparse_set_idx.push(i + data_len);
        }

        let size = self.manage_int(capa as isize);
        let min = self.manage_int(0);
        let max = self.manage_int(n as isize - 1);

        self.sparse_sets.push(SparseSet {
            val_offset,
            start,
            capa,
            size,
            min,
            max,
        });
        ReversibleSparseSet(id)
    }
    /// returns the size of the given sparse set
    pub fn sparse_set_size(&self, id: ReversibleSparseSet) -> usize {
        self.get_int(self.sparse_sets[id.0].size) as usize
    }
    /// returns true iff the sparse set is empty
    pub fn sparse_set_is_empty(&self, id: ReversibleSparseSet) -> bool {
        self.sparse_set_size(id) == 0
    }
    /// returns the minimum value of the sparse set (if it exists)
    pub fn sparse_set_get_min(&self, id: ReversibleSparseSet) -> Option<isize> {
        let ss = self.sparse_sets[id.0];
        if self.get_int(ss.size) <= 0 {
            None
        } else {
            Some(self.get_int(ss.min) + ss.val_offset)
        }
    }
    /// returns the maximum value of the sparse set (if it exists)
    pub fn sparse_set_get_max(&self, id: ReversibleSparseSet) -> Option<isize> {
        let ss = self.sparse_sets[id.0];
        if self.get_int(ss.size) <= 0 {
            None
        } else {
            Some(self.get_int(ss.max) + ss.val_offset)
        }
    }
    /// returns true iff the sparse set contains the designated value
    pub fn sparse_set_contains(&self, id: ReversibleSparseSet, value: isize) -> bool {
        let ss = self.sparse_sets[id.0];
        let val = value - ss.val_offset;

        if val < 0 || val >= ss.capa as isize {
            false
        } else {
            self.sparse_set_idx[val as usize] < self.get_int(ss.size) as usize
        }
    }
    /// removes the given value from the sparse set and returns a boolean telling
    /// whether or not the value was actually deleted from the set
    pub fn sparse_set_remove(&mut self, id: ReversibleSparseSet, value: isize) -> bool {
        if !self.sparse_set_contains(id, value) {
            false
        } else {
            let ss = self.sparse_sets[id.0];
            let val = (value - ss.val_offset) as usize;
            let size = self.get_int(ss.size) as usize;

            let a = val;
            let b = self.sparse_set_data[ss.start + size - 1];
            self.sparse_set_swap(a, b);

            let size = self.decrement(ss.size) as usize;

            // maintain the bounds
            self.sparse_set_update_min_val_removed(ss, size, val);
            self.sparse_set_update_max_val_removed(ss, size, val);

            true
        }
    }

    /// removes all values in the set
    pub fn sparse_set_remove_all(&mut self, id: ReversibleSparseSet) {
        self.set_int(self.sparse_sets[id.0].size, 0);
    }

    /// removes all values in the set
    pub fn sparse_set_remove_all_but(&mut self, id: ReversibleSparseSet, value: isize) {
        if self.sparse_set_contains(id, value) {
            // in this case, it suffices to place the desired item in position 0
            let ss = self.sparse_sets[id.0];
            let val = (value - ss.val_offset) as usize;

            let a = val;
            let b = self.sparse_set_data[ss.start];
            self.sparse_set_swap(a, b);

            self.set_int(ss.size, 1);
            self.set_int(ss.min, val as isize);
            self.set_int(ss.max, val as isize);
        } else {
            self.sparse_set_remove_all(id);
        }
    }

    /// remove from the set all the items having a value lower than the given
    /// `value`
    pub fn sparse_set_remove_below(&mut self, id: ReversibleSparseSet, val: isize) {
        let ss = self.sparse_sets[id.0];
        let val = val - ss.val_offset;
        let empty = self.get_int(ss.size) == 0;

        if !empty {
            let max = self.get_int(ss.max);
            if val > max {
                self.sparse_set_remove_all(id);
            } else {
                let min = self.get_int(ss.min);
                for x in min..val {
                    self.sparse_set_remove(id, x + ss.val_offset);
                }
            }
        }
    }
    /// remove from the set all the items having a value higher than the given
    /// `value`
    pub fn sparse_set_remove_above(&mut self, id: ReversibleSparseSet, val: isize) {
        let ss = self.sparse_sets[id.0];
        let val = val - ss.val_offset;
        let empty = self.get_int(ss.size) == 0;

        if !empty {
            let min = self.get_int(ss.min);
            if val < min {
                self.sparse_set_remove_all(id);
            } else {
                let max = self.get_int(ss.max);
                for x in val + 1..=max {
                    self.sparse_set_remove(id, x + ss.val_offset);
                }
            }
        }
    }

    //~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    // private methods
    //~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    /// swaps the items at indices a and b in the sparse set
    fn sparse_set_swap(&mut self, a: usize, b: usize) {
        let ia = self.sparse_set_idx[a];
        let ib = self.sparse_set_idx[b];
        self.sparse_set_data.swap(ia, ib);
        self.sparse_set_idx.swap(a, b)
    }
    /// update the minimum
    fn sparse_set_update_min_val_removed(&mut self, ss: SparseSet, size: usize, val: usize) {
        let min = self.get_int(ss.min) as usize;

        if size > 0 && min == val {
            let min = self.sparse_set_data[ss.start..ss.start + size]
                .iter()
                .min()
                .copied()
                .unwrap(); // this is guaranteed to be ok since the set is not empty
            self.set_int(ss.min, min as isize);
        }
    }
    /// update the maximux
    fn sparse_set_update_max_val_removed(&mut self, ss: SparseSet, size: usize, val: usize) {
        let max = self.get_int(ss.max) as usize;

        if size > 0 && max == val {
            let max = self.sparse_set_data[ss.start..ss.start + size]
                .iter()
                .max()
                .copied()
                .unwrap(); // this is guaranteed to be ok since the set is not empty
            self.set_int(ss.max, max as isize);
        }
    }
}

//------------------------------------------------------------------------------
// LOW LEVEL MANAGEMENT
//------------------------------------------------------------------------------

/// Uniquely identifies a managed resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Reversible(usize);

/// This is the structure which is in charge of guaranteeing that all data
/// are properly saved and restored as though they were pushed on a stack
#[derive(Debug, Clone, Default)]
pub struct StateManager<T>
where
    T: Eq + Copy,
{
    /// At what 'time' was this data modified to the point where it needed being saved ?
    ///
    /// # Note:
    /// This data was referred to as 'magic' in minicp and maxicp. Still I like to
    /// convey the idea that 'magic' is actually a monotonic clock  indicating the validity
    /// timestamp of the data.
    clock: usize,

    /// The current value of the various managed data
    current: Vec<TrailEntry<T>>,
    /// The previous values that are saved on the trail
    trail: Vec<TrailEntry<T>>,
    /// The various 'levels' of data that have been 'push' and 'pop' separated
    levels: Vec<Level>,
}

impl<T> StateManager<T>
where
    T: Eq + Copy,
{
    /// creates a new empty state manager
    pub fn new() -> Self {
        Self {
            clock: 0,
            current: vec![],
            trail: vec![],
            levels: vec![Level {
                trail_size: 0,
                accessible: 0,
            }],
        }
    }

    /// creates a new managed resource and returns its identifier
    pub fn manage(&mut self, value: T) -> Reversible {
        let id = Reversible(self.current.len());
        self.current.push(TrailEntry {
            id,
            clock: self.clock,
            value,
        });
        id
    }

    /// retrieves the value of the given resource
    pub fn get_value(&self, id: Reversible) -> T {
        self.current[id.0].value
    }

    /// sets the value of the given resource and returns the new value of that resource
    pub fn set_value(&mut self, id: Reversible, value: T) -> T {
        let curr = self.current[id.0];
        // if the value is unchanged there is no need to do anything
        if value != curr.value {
            // do i need to trail this data ?
            if curr.clock < self.clock {
                self.trail.push(curr);
                self.current[id.0] = TrailEntry {
                    id,
                    clock: self.clock,
                    value,
                }
            // apparently i don't need to save it on the trail. i can modify it right away
            } else {
                self.current[id.0].value = value;
            }
        }

        value
    }

    /// save the current state and make it restoreable
    pub fn push(&mut self) {
        self.clock += 1;
        self.levels.push(Level {
            trail_size: self.trail.len(),
            accessible: self.current.len(),
        })
    }

    /// restore the current state
    pub fn pop(&mut self) {
        let level = self
            .levels
            .pop()
            .expect("cannot pop above the root level of the state manager");
        for e in self.trail.iter().skip(level.trail_size).rev().copied() {
            self.current[e.id.0] = e;
        }
        self.trail.truncate(level.trail_size);
        self.current.truncate(level.accessible);
    }
}

impl StateManager<bool> {
    /// Negates the value
    pub fn flip(&mut self, id: Reversible) -> bool {
        self.set_value(id, self.get_value(id).not())
    }
}

impl<T> StateManager<T>
where
    T: Int,
{
    /// Increments the value
    pub fn increment(&mut self, id: Reversible) -> T {
        self.set_value(id, self.get_value(id) + T::one())
    }
    /// Decrements the value
    pub fn decrement(&mut self, id: Reversible) -> T {
        self.set_value(id, self.get_value(id) - T::one())
    }
}

/// An entry that is used to save/restore data from the trail
#[derive(Debug, Clone, Copy)]
struct TrailEntry<T>
where
    T: Eq + Copy,
{
    /// The identifier of the managed resource
    id: Reversible,
    /// At what 'time' was this data modified to the point where it needed being saved ?
    ///
    /// # Note:
    /// This data was referred to as 'magic' in minicp and maxicp. Still I like to
    /// convey the idea that 'magic' is actually a monotonic clock  indicating the validity
    /// timestamp of the data.
    clock: usize,
    /// The value that will be restored in the managed data
    value: T,
}

/// This structure keeps track of the information about one given level: the length of its
/// trail and the count of variables that are managed by the state manager
#[derive(Debug, Clone, Copy, Default)]
struct Level {
    trail_size: usize,
    accessible: usize,
}

// #############################################################################
// ### UNIT TESTS ##############################################################
// #############################################################################

#[cfg(test)]
mod tests_manager_bool {
    use super::*;

    #[test]
    fn it_works() {
        let mut mgr = SimpleManager::new();

        let a = mgr.manage_bool(false);
        assert!(!mgr.get_bool(a));

        mgr.push();
        assert!(!mgr.get_bool(a));

        mgr.set_bool(a, true);
        assert!(mgr.get_bool(a));

        mgr.push();
        assert!(mgr.get_bool(a));

        mgr.set_bool(a, false);
        assert!(!mgr.get_bool(a));

        mgr.set_bool(a, true);
        assert!(mgr.get_bool(a));

        mgr.pop();
        assert!(mgr.get_bool(a));

        mgr.pop();
        assert!(!mgr.get_bool(a));
    }

    #[test]
    #[should_panic]
    fn one_cannot_use_an_item_that_has_been_managed_at_a_later_stage() {
        let mut mgr = SimpleManager::new();

        let a = mgr.manage_bool(false);
        assert!(!mgr.get_bool(a));

        mgr.push();
        let b = mgr.manage_bool(false);

        assert!(!mgr.get_bool(a));
        assert!(!mgr.get_bool(b));

        mgr.set_bool(a, true);
        assert!(mgr.get_bool(a));
        assert!(!mgr.get_bool(b));

        mgr.pop();
        assert!(!mgr.get_bool(a));
        mgr.get_bool(b); // this is where the panic must occur
    }
}

#[cfg(test)]
mod tests_manager_int {
    use super::*;

    #[test]
    fn it_works() {
        let mut mgr = SimpleManager::new();

        let a = mgr.manage_int(42);
        assert_eq!(mgr.get_int(a), 42);

        mgr.push();
        assert_eq!(mgr.get_int(a), 42);

        mgr.set_int(a, 64);
        assert_eq!(mgr.get_int(a), 64);

        mgr.push();
        assert_eq!(mgr.get_int(a), 64);

        mgr.set_int(a, 72);
        assert_eq!(mgr.get_int(a), 72);

        mgr.set_int(a, 96);
        assert_eq!(mgr.get_int(a), 96);

        mgr.pop();
        assert_eq!(mgr.get_int(a), 64);

        mgr.pop();
        assert_eq!(mgr.get_int(a), 42);
    }

    #[test]
    #[should_panic]
    fn one_cannot_use_an_item_that_has_been_managed_at_a_later_stage() {
        let mut mgr = SimpleManager::new();

        let a = mgr.manage_int(0);
        assert_eq!(mgr.get_int(a), 0);

        mgr.push();
        let b = mgr.manage_int(10);

        assert_eq!(mgr.get_int(a), 0);
        assert_eq!(mgr.get_int(b), 10);

        mgr.set_int(a, 2);
        assert_eq!(mgr.get_int(a), 2);
        assert_eq!(mgr.get_int(b), 10);

        mgr.pop();
        assert_eq!(mgr.get_int(a), 0);
        mgr.get_int(b); // this is where the panic must occur
    }
}

#[cfg(test)]
mod tests_manager_sparse_set {
    use crate::SimpleManager;

    #[test]
    fn contains() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(10, 0);

        assert!(mgr.sparse_set_contains(ss, 5));
        mgr.push();
        assert!(mgr.sparse_set_contains(ss, 5));

        mgr.sparse_set_remove(ss, 5);
        assert!(!mgr.sparse_set_contains(ss, 5));

        mgr.pop();
        assert!(mgr.sparse_set_contains(ss, 5));
    }
    #[test]
    fn contains_is_always_false_for_items_not_supposed_to_be_in_set() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        assert!(!mgr.sparse_set_contains(ss, 5));
        assert!(!mgr.sparse_set_contains(ss, 3));
        assert!(!mgr.sparse_set_contains(ss, -3));
        assert!(!mgr.sparse_set_contains(ss, -5));
    }

    #[test]
    fn is_empty() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        mgr.push();
        assert!(!mgr.sparse_set_is_empty(ss));
        mgr.sparse_set_remove(ss, 0);
        assert!(!mgr.sparse_set_is_empty(ss));
        mgr.sparse_set_remove(ss, 1);
        assert!(!mgr.sparse_set_is_empty(ss));
        mgr.sparse_set_remove(ss, 2);

        // now it is empty
        assert!(mgr.sparse_set_is_empty(ss));
        mgr.pop();
        assert!(!mgr.sparse_set_is_empty(ss));
    }

    #[test]
    fn size() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        mgr.push();
        assert_eq!(mgr.sparse_set_size(ss), 3);
        mgr.sparse_set_remove(ss, 0);
        assert_eq!(mgr.sparse_set_size(ss), 2);
        mgr.sparse_set_remove(ss, 1);
        assert_eq!(mgr.sparse_set_size(ss), 1);
        mgr.sparse_set_remove(ss, 2);

        // now it is empty
        assert_eq!(mgr.sparse_set_size(ss), 0);
        mgr.pop();
        assert_eq!(mgr.sparse_set_size(ss), 3);
    }

    #[test]
    fn get_max_decreases_when_ub_drops() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        mgr.push();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
        mgr.sparse_set_remove(ss, 2);

        mgr.push();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(1));
        mgr.sparse_set_remove(ss, 1);

        mgr.push();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(0));

        mgr.sparse_set_remove(ss, 0);
        assert_eq!(mgr.sparse_set_get_max(ss), None);

        mgr.pop();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(0));
        mgr.pop();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(1));
        mgr.pop();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
    }
    #[test]
    fn get_max_is_not_affected_by_holes() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        mgr.push();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
        mgr.sparse_set_remove(ss, 0);

        mgr.push();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
        mgr.sparse_set_remove(ss, 1);

        mgr.push();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
        mgr.sparse_set_remove(ss, 2);

        assert_eq!(mgr.sparse_set_get_max(ss), None);

        mgr.pop();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
        mgr.pop();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
        mgr.pop();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
    }

    #[test]
    fn get_min_increases_when_lb_bumps() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        mgr.push();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
        mgr.sparse_set_remove(ss, 0);

        mgr.push();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(1));
        mgr.sparse_set_remove(ss, 1);

        mgr.push();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(2));

        mgr.sparse_set_remove(ss, 2);
        assert_eq!(mgr.sparse_set_get_min(ss), None);

        mgr.pop();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(2));
        mgr.pop();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(1));
        mgr.pop();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
    }

    #[test]
    fn get_min_is_not_affected_by_holes() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        mgr.push();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
        mgr.sparse_set_remove(ss, 2);

        mgr.push();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
        mgr.sparse_set_remove(ss, 1);

        mgr.push();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
        mgr.sparse_set_remove(ss, 0);

        assert_eq!(mgr.sparse_set_get_min(ss), None);

        mgr.pop();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
        mgr.pop();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
        mgr.pop();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
    }

    #[test]
    fn remove_all() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(3, 0);
        assert!(!mgr.sparse_set_is_empty(ss));

        mgr.push();
        mgr.sparse_set_remove_all(ss);
        assert!(mgr.sparse_set_is_empty(ss));

        mgr.pop();
        assert!(!mgr.sparse_set_is_empty(ss));
    }

    #[test]
    fn remove() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        assert!(mgr.sparse_set_contains(ss, 1));
        mgr.push();
        mgr.sparse_set_remove(ss, 1);
        assert!(!mgr.sparse_set_contains(ss, 1));
        mgr.pop();
        assert!(mgr.sparse_set_contains(ss, 1));
    }

    #[test]
    fn remove_above() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(10, 0);

        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_get_max(ss), Some(9));

        mgr.push();
        mgr.sparse_set_remove_above(ss, 5);
        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_get_max(ss), Some(5));

        mgr.pop();
        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_get_max(ss), Some(9));
    }
    #[test]
    fn remove_above_max_does_nothing() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(10, 0);

        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_size(ss), 10);
        assert_eq!(mgr.sparse_set_get_max(ss), Some(9));

        mgr.sparse_set_remove_above(ss, 10);
        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_size(ss), 10);
        assert_eq!(mgr.sparse_set_get_max(ss), Some(9));
    }
    #[test]
    fn remove_above_min_empties_set() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(10, 0);

        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_size(ss), 10);
        assert_eq!(mgr.sparse_set_get_max(ss), Some(9));

        mgr.sparse_set_remove_above(ss, -1);
        assert!(mgr.sparse_set_is_empty(ss));
    }

    #[test]
    fn remove_below() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(10, 0);

        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));

        mgr.push();
        mgr.sparse_set_remove_below(ss, 5);
        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_get_min(ss), Some(5));

        mgr.pop();
        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
    }
    #[test]
    fn remove_below_min_does_nothing() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(10, 0);

        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_size(ss), 10);
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));

        mgr.sparse_set_remove_below(ss, -1);
        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_size(ss), 10);
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
    }
    #[test]
    fn remove_below_max_empties_set() {
        let mut mgr = SimpleManager::new();
        let ss = mgr.manage_sparse_set(10, 0);

        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_size(ss), 10);
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));

        mgr.sparse_set_remove_below(ss, 10);
        assert!(mgr.sparse_set_is_empty(ss));
    }
}

#[cfg(test)]
mod tests_basic_manager {
    use super::*;

    #[test]
    fn it_works() {
        let mut mgr = StateManager::<isize>::new();

        let a = mgr.manage(0);
        assert_eq!(mgr.get_value(a), 0);

        mgr.push();
        assert_eq!(mgr.get_value(a), 0);

        mgr.set_value(a, 1);
        assert_eq!(mgr.get_value(a), 1);

        mgr.push();
        assert_eq!(mgr.get_value(a), 1);

        mgr.set_value(a, 2);
        assert_eq!(mgr.get_value(a), 2);

        mgr.set_value(a, 42);
        assert_eq!(mgr.get_value(a), 42);

        mgr.pop();
        assert_eq!(mgr.get_value(a), 1);

        mgr.pop();
        assert_eq!(mgr.get_value(a), 0);
    }

    #[test]
    #[should_panic]
    fn one_cannot_use_an_item_that_has_been_managed_at_a_later_stage() {
        let mut mgr = StateManager::<isize>::new();

        let a = mgr.manage(10);
        assert_eq!(mgr.get_value(a), 10);

        mgr.push();
        let b = mgr.manage(20);

        assert_eq!(mgr.get_value(a), 10);
        assert_eq!(mgr.get_value(b), 20);

        mgr.set_value(a, 30);
        assert_eq!(mgr.get_value(a), 30);
        assert_eq!(mgr.get_value(b), 20);

        mgr.pop();
        assert_eq!(mgr.get_value(a), 10);
        mgr.get_value(b); // this is where the panic must occur
    }
}
