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
use super::*;

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~ TRAIL DATA ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// This structure keeps track of the information about one given level: the
/// length of its trail and the count of each kind of resources that are managed
/// by the state manager
#[derive(Debug, Clone, Copy, Default)]
struct Level {
    /// the length of the trail at the moment this layer was started
    trail_size: usize,

    /// how many integers have already been recorded ? (note: booleans are
    /// simply mqpped onto integers)
    integers: usize,

    /// how many intervals have already been defined ?
    intervals: usize,

    /// how many sparse sets have already been recorded ?
    sparse_sets: usize,
    /// length of the sparse sets data
    sparse_set_data: usize,
}

/// An entry that is used to save/restore data from the trail
#[derive(Debug, Clone, Copy)]
enum TrailEntry {
    /// An entry related to the restoration of an integer value
    IntEntry(IntState),
}

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~ STATE MANAGER ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/// A simple state manager that can manage booleans, integers, sparse sets,
/// intervals, lazy sparse sets .. and so on (basically any reversible data
/// structure ends up being managed by this struct)
#[derive(Debug, Clone)]
pub struct TrailedStateManager {
    /// At what 'time' was this data modified to the point where it needed being saved ?
    ///
    /// # Note:
    /// This data was referred to as 'magic' in minicp and maxicp. Still I like to
    /// convey the idea that 'magic' is actually a monotonic clock  indicating the validity
    /// timestamp of the data.
    clock: usize,
    /// The previous values that are saved on the trail
    trail: Vec<TrailEntry>,
    /// Some book keeping to track what needs and what doesn't need
    /// to be restored upon manager `pop`
    levels: Vec<Level>,

    /// The current value of the various managed data
    integers: Vec<IntState>,

    /// The intervals that have been defined
    intervals: Vec<Interval>,

    /// Holds the metadata about sparse sets
    sparse_sets: Vec<SparseSet>,
    /// Holds the actual content of the sparse sets
    sparse_set_data: Vec<usize>,
    /// Holds the indices of the data in a sparse set
    sparse_set_idx: Vec<usize>,
}
impl Default for TrailedStateManager {
    fn default() -> Self {
        Self::new()
    }
}
impl TrailedStateManager {
    /// Creates a new SimpleManager
    pub fn new() -> Self {
        Self {
            clock: 0,
            trail: vec![],
            //
            integers: vec![],
            //
            intervals: vec![],
            //
            sparse_sets: vec![],
            sparse_set_data: vec![],
            sparse_set_idx: vec![],

            levels: vec![Level {
                trail_size: 0,
                integers: 0,
                intervals: 0,
                sparse_sets: 0,
                sparse_set_data: 0,
            }],
        }
    }
}
impl StateManager for TrailedStateManager {}
//------------------------------------------------------------------------------
// Save and Restore management
//------------------------------------------------------------------------------
impl SaveAndRestore for TrailedStateManager {
    /// Saves the current state
    fn save_state(&mut self) {
        self.clock += 1;

        // additional book keeping
        self.levels.push(Level {
            trail_size: self.trail.len(),
            //
            integers: self.integers.len(),
            //
            intervals: self.intervals.len(),
            //
            sparse_sets: self.sparse_sets.len(),
            sparse_set_data: self.sparse_set_data.len(),
        })
    }
    /// Restores the previous state
    fn restore_state(&mut self) {
        let level = self
            .levels
            .pop()
            .expect("cannot pop above the root level of the state manager");

        // restore whatever needs to be restored
        for e in self.trail.iter().skip(level.trail_size).rev().copied() {
            match e {
                TrailEntry::IntEntry(state) => self.integers[state.id.0] = state,
            }
        }
        // drop stale trail entry
        self.trail.truncate(level.trail_size);

        // integers book keeping
        self.integers.truncate(level.integers);
        // intervals book keeping
        self.intervals.truncate(level.intervals);
        // sparse set book keeping
        self.sparse_sets.truncate(level.sparse_sets);
        self.sparse_set_data.truncate(level.sparse_set_data);
    }
}
//------------------------------------------------------------------------------
// Int management
//------------------------------------------------------------------------------
/// The state of an integer that can be saved and restored
#[derive(Debug, Clone, Copy)]
struct IntState {
    /// The identifier of the managed resource
    id: ReversibleInt,
    /// At what 'time' was this data modified to the point where it needed being saved ?
    ///
    /// # Note:
    /// This data was referred to as 'magic' in minicp and maxicp. Still I like to
    /// convey the idea that 'magic' is actually a monotonic clock  indicating the validity
    /// timestamp of the data.
    clock: usize,
    /// The value that will be restored in the managed data
    value: isize,
}

impl IntManager for TrailedStateManager {
    /// creates a new managed integer
    fn manage_int(&mut self, value: isize) -> ReversibleInt {
        let id = ReversibleInt(self.integers.len());
        self.integers.push(IntState {
            id,
            clock: self.clock,
            value,
        });
        id
    }
    /// returns the value of a managed integer
    fn get_int(&self, id: ReversibleInt) -> isize {
        self.integers[id.0].value
    }
    /// sets a managed integer's value and returns the new value
    fn set_int(&mut self, id: ReversibleInt, value: isize) -> isize {
        let curr = self.integers[id.0];
        // if the value is unchanged there is no need to do anything
        if value != curr.value {
            // do i need to trail this data ?
            if curr.clock < self.clock {
                self.trail.push(TrailEntry::IntEntry(curr));
                self.integers[id.0] = IntState {
                    id,
                    clock: self.clock,
                    value,
                }
            // apparently i don't need to save it on the trail. i can modify it right away
            } else {
                self.integers[id.0].value = value;
            }
        }
        value
    }
    /// increments a managed integer's value
    fn increment(&mut self, id: ReversibleInt) -> isize {
        self.set_int(id, self.get_int(id) + 1)
    }
    /// decrements a managed integer's value
    fn decrement(&mut self, id: ReversibleInt) -> isize {
        self.set_int(id, self.get_int(id) - 1)
    }
}
//------------------------------------------------------------------------------
// Bool management
//------------------------------------------------------------------------------
impl BoolManager for TrailedStateManager {
    /// creates a new managed boolean
    fn manage_bool(&mut self, v: bool) -> ReversibleBool {
        ReversibleBool(self.manage_int(v as isize))
    }
    /// returns the value of a managed boolean
    fn get_bool(&self, id: ReversibleBool) -> bool {
        self.get_int(id.0) != 0
    }
    /// sets a managed boolean's value and returns the new value
    fn set_bool(&mut self, id: ReversibleBool, value: bool) -> bool {
        self.set_int(id.0, value as isize) != 0
    }
}
//------------------------------------------------------------------------------
// Interval management
//------------------------------------------------------------------------------
/// This structure tracks the information that needs to be maintained when
/// working with a managed interval
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Interval {
    /// the minimum value in the interval (included !)
    min: ReversibleInt,
    /// the maximum value in the interval (included !)
    max: ReversibleInt,
}
impl IntervalManager for TrailedStateManager {
    /// creates a new managed interval low..=high (that is, an interval where
    /// both ends are included in the interval)
    ///
    /// # Parameters
    /// - low: the lowest possible value in this interval (included)
    /// - high: the highest possible value in this interval (included)
    fn manage_interval(&mut self, low: isize, high: isize) -> ReversibleInterval {
        let id = ReversibleInterval(self.intervals.len());
        let min = self.manage_int(low);
        let max = self.manage_int(high);
        self.intervals.push(Interval { min, max });
        id
    }
    /// Returns true iff the interval is empty
    fn interval_is_empty(&self, id: ReversibleInterval) -> bool {
        self.interval_size(id) == 0
    }
    /// Returns the number of integer values in the interval
    fn interval_size(&self, id: ReversibleInterval) -> usize {
        let interval = self.intervals[id.0];
        0.max(1 + self.get_int(interval.max) - self.get_int(interval.min)) as usize
    }
    /// Returns the minimum integer value in the interval (if there is one)
    fn interval_get_min(&self, id: ReversibleInterval) -> Option<isize> {
        let interval = self.intervals[id.0];
        let min = self.get_int(interval.min);
        let max = self.get_int(interval.max);

        if min <= max {
            Some(min)
        } else {
            None
        }
    }
    /// Returns the maximum integer value in the interval (if there is one)
    fn interval_get_max(&self, id: ReversibleInterval) -> Option<isize> {
        let interval = self.intervals[id.0];
        let min = self.get_int(interval.min);
        let max = self.get_int(interval.max);

        if min <= max {
            Some(max)
        } else {
            None
        }
    }
    /// Returns true iff the given interval comprises the specified value
    fn interval_contains(&self, id: ReversibleInterval, value: isize) -> bool {
        let interval = self.intervals[id.0];
        let min = self.get_int(interval.min);
        let max = self.get_int(interval.max);

        min <= value && value <= max
    }
    /// removes all values in the interval except the given value (if it belongs to the set)
    fn interval_remove_all_but(&mut self, id: ReversibleInterval, value: isize) {
        if self.interval_contains(id, value) {
            let interval = self.intervals[id.0];
            self.set_int(interval.min, value);
            self.set_int(interval.max, value);
        } else {
            self.interval_remove_all(id);
        }
    }
    /// removes all values in the interval
    fn interval_remove_all(&mut self, id: ReversibleInterval) {
        let interval = self.intervals[id.0];
        let min = self.get_int(interval.min);
        self.set_int(interval.min, 1 + min);
        self.set_int(interval.max, min);
    }
    /// remove from the set all the items having a value lower than the given
    /// `value`
    fn interval_remove_below(&mut self, id: ReversibleInterval, value: isize) {
        let interval = self.intervals[id.0];
        let min = self.get_int(interval.min);
        self.set_int(interval.min, value.max(min));
    }
    /// remove from the set all the items having a value greater than the given
    /// `value`
    fn interval_remove_above(&mut self, id: ReversibleInterval, value: isize) {
        let interval = self.intervals[id.0];
        let max = self.get_int(interval.max);
        self.set_int(interval.max, value.min(max));
    }

    fn interval_for_each<F: FnMut(isize)>(&self, id: ReversibleInterval, f: F) {
        let interval = self.intervals[id.0];
        let min = self.get_int(interval.min);
        let max = self.get_int(interval.max);

        (min..=max).for_each(f)
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
    /// the minimum value in the set (included !)
    min: ReversibleInt,
    /// the maximum value in the set (included !)
    max: ReversibleInt,
}
impl SparseSetManager for TrailedStateManager {
    /// creates a new managed sparse set with values
    /// [0 + value_offset, 1 + value_offset, 2 + value_offset, ... , n-1 + value_offset]
    ///
    /// # Params
    /// - n: the number of values in the sparse set
    /// - val_offset: the "offset" of the first value that belongs to the set
    fn manage_sparse_set(&mut self, n: usize, val_offset: isize) -> ReversibleSparseSet {
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
    fn sparse_set_size(&self, id: ReversibleSparseSet) -> usize {
        self.get_int(self.sparse_sets[id.0].size) as usize
    }
    /// returns true iff the sparse set is empty
    fn sparse_set_is_empty(&self, id: ReversibleSparseSet) -> bool {
        self.sparse_set_size(id) == 0
    }
    /// returns the minimum value of the sparse set (if it exists)
    fn sparse_set_get_min(&self, id: ReversibleSparseSet) -> Option<isize> {
        let ss = self.sparse_sets[id.0];
        if self.get_int(ss.size) <= 0 {
            None
        } else {
            Some(self.get_int(ss.min) + ss.val_offset)
        }
    }
    /// returns the maximum value of the sparse set (if it exists)
    fn sparse_set_get_max(&self, id: ReversibleSparseSet) -> Option<isize> {
        let ss = self.sparse_sets[id.0];
        if self.get_int(ss.size) <= 0 {
            None
        } else {
            Some(self.get_int(ss.max) + ss.val_offset)
        }
    }
    /// returns true iff the sparse set contains the designated value
    fn sparse_set_contains(&self, id: ReversibleSparseSet, value: isize) -> bool {
        let ss = self.sparse_sets[id.0];
        let val = value - ss.val_offset;

        if val < 0 || val >= ss.capa as isize {
            false
        } else {
            let sz = self.get_int(ss.size) as usize;
            self.sparse_set_idx[ss.start + val as usize] < sz + ss.start
        }
    }
    /// removes the given value from the sparse set and returns a boolean telling
    /// whether or not the value was actually deleted from the set
    fn sparse_set_remove(&mut self, id: ReversibleSparseSet, value: isize) -> bool {
        if !self.sparse_set_contains(id, value) {
            false
        } else {
            let ss = self.sparse_sets[id.0];
            let val = (value - ss.val_offset) as usize;
            let size = self.get_int(ss.size) as usize;

            let a = ss.start + val;
            let b = ss.start + self.sparse_set_data[ss.start + size - 1];
            self.sparse_set_swap(a, b);

            let size = self.decrement(ss.size) as usize;

            // maintain the bounds
            self.sparse_set_update_min_val_removed(ss, size, val);
            self.sparse_set_update_max_val_removed(ss, size, val);

            true
        }
    }

    /// removes all values in the set
    fn sparse_set_remove_all(&mut self, id: ReversibleSparseSet) {
        self.set_int(self.sparse_sets[id.0].size, 0);
    }

    /// removes all values in the set except the given value (if it belongs to the set)
    fn sparse_set_remove_all_but(&mut self, id: ReversibleSparseSet, value: isize) {
        if self.sparse_set_contains(id, value) {
            // in this case, it suffices to place the desired item in position 0
            let ss = self.sparse_sets[id.0];
            let val = (value - ss.val_offset) as usize;

            let a = ss.start + val;
            let b = ss.start + self.sparse_set_data[ss.start];
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
    fn sparse_set_remove_below(&mut self, id: ReversibleSparseSet, val: isize) {
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
    fn sparse_set_remove_above(&mut self, id: ReversibleSparseSet, val: isize) {
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
    /// Returns an iterator over the values from the sparse set
    fn sparse_set_for_each<F: FnMut(isize)>(&self, id: ReversibleSparseSet, f: F) {
        let ss = self.sparse_sets[id.0];
        let len = self.get_int(ss.size) as usize;

        self.sparse_set_data
            .iter()
            .skip(ss.start)
            .take(len)
            .map(|v| *v as isize + ss.val_offset)
            .for_each(f)
    }
}
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// private methods
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
impl TrailedStateManager {
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

// #############################################################################
// ### UNIT TESTS ##############################################################
// #############################################################################

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~ UT BOOLEAN ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#[cfg(test)]
mod tests_manager_bool {
    use super::*;

    #[test]
    fn it_works() {
        let mut mgr = TrailedStateManager::new();

        let a = mgr.manage_bool(false);
        assert!(!mgr.get_bool(a));

        mgr.save_state();
        assert!(!mgr.get_bool(a));

        mgr.set_bool(a, true);
        assert!(mgr.get_bool(a));

        mgr.save_state();
        assert!(mgr.get_bool(a));

        mgr.set_bool(a, false);
        assert!(!mgr.get_bool(a));

        mgr.set_bool(a, true);
        assert!(mgr.get_bool(a));

        mgr.restore_state();
        assert!(mgr.get_bool(a));

        mgr.restore_state();
        assert!(!mgr.get_bool(a));
    }

    #[test]
    #[should_panic]
    fn one_cannot_use_an_item_that_has_been_managed_at_a_later_stage() {
        let mut mgr = TrailedStateManager::new();

        let a = mgr.manage_bool(false);
        assert!(!mgr.get_bool(a));

        mgr.save_state();
        let b = mgr.manage_bool(false);

        assert!(!mgr.get_bool(a));
        assert!(!mgr.get_bool(b));

        mgr.set_bool(a, true);
        assert!(mgr.get_bool(a));
        assert!(!mgr.get_bool(b));

        mgr.restore_state();
        assert!(!mgr.get_bool(a));
        mgr.get_bool(b); // this is where the panic must occur
    }
}

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~ UT INTEGER ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#[cfg(test)]
mod tests_manager_int {
    use super::*;

    #[test]
    fn it_works() {
        let mut mgr = TrailedStateManager::new();

        let a = mgr.manage_int(42);
        assert_eq!(mgr.get_int(a), 42);

        mgr.save_state();
        assert_eq!(mgr.get_int(a), 42);

        mgr.set_int(a, 64);
        assert_eq!(mgr.get_int(a), 64);

        mgr.save_state();
        assert_eq!(mgr.get_int(a), 64);

        mgr.set_int(a, 72);
        assert_eq!(mgr.get_int(a), 72);

        mgr.set_int(a, 96);
        assert_eq!(mgr.get_int(a), 96);

        mgr.restore_state();
        assert_eq!(mgr.get_int(a), 64);

        mgr.restore_state();
        assert_eq!(mgr.get_int(a), 42);
    }

    #[test]
    #[should_panic]
    fn one_cannot_use_an_item_that_has_been_managed_at_a_later_stage() {
        let mut mgr = TrailedStateManager::new();

        let a = mgr.manage_int(0);
        assert_eq!(mgr.get_int(a), 0);

        mgr.save_state();
        let b = mgr.manage_int(10);

        assert_eq!(mgr.get_int(a), 0);
        assert_eq!(mgr.get_int(b), 10);

        mgr.set_int(a, 2);
        assert_eq!(mgr.get_int(a), 2);
        assert_eq!(mgr.get_int(b), 10);

        mgr.restore_state();
        assert_eq!(mgr.get_int(a), 0);
        mgr.get_int(b); // this is where the panic must occur
    }
}
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~ UT SPARSE SET ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#[cfg(test)]
mod tests_manager_sparse_set {
    use super::*;

    #[test]
    fn contains() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(10, 0);

        assert!(mgr.sparse_set_contains(ss, 5));
        mgr.save_state();
        assert!(mgr.sparse_set_contains(ss, 5));

        mgr.sparse_set_remove(ss, 5);
        assert!(!mgr.sparse_set_contains(ss, 5));

        mgr.restore_state();
        assert!(mgr.sparse_set_contains(ss, 5));
    }
    #[test]
    fn contains_is_always_false_for_items_not_supposed_to_be_in_set() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        assert!(!mgr.sparse_set_contains(ss, 5));
        assert!(!mgr.sparse_set_contains(ss, 3));
        assert!(!mgr.sparse_set_contains(ss, -3));
        assert!(!mgr.sparse_set_contains(ss, -5));
    }

    #[test]
    fn is_empty() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        mgr.save_state();
        assert!(!mgr.sparse_set_is_empty(ss));
        mgr.sparse_set_remove(ss, 0);
        assert!(!mgr.sparse_set_is_empty(ss));
        mgr.sparse_set_remove(ss, 1);
        assert!(!mgr.sparse_set_is_empty(ss));
        mgr.sparse_set_remove(ss, 2);

        // now it is empty
        assert!(mgr.sparse_set_is_empty(ss));
        mgr.restore_state();
        assert!(!mgr.sparse_set_is_empty(ss));
    }

    #[test]
    fn size() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        mgr.save_state();
        assert_eq!(mgr.sparse_set_size(ss), 3);
        mgr.sparse_set_remove(ss, 0);
        assert_eq!(mgr.sparse_set_size(ss), 2);
        mgr.sparse_set_remove(ss, 1);
        assert_eq!(mgr.sparse_set_size(ss), 1);
        mgr.sparse_set_remove(ss, 2);

        // now it is empty
        assert_eq!(mgr.sparse_set_size(ss), 0);
        mgr.restore_state();
        assert_eq!(mgr.sparse_set_size(ss), 3);
    }

    #[test]
    fn get_max_decreases_when_ub_drops() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        mgr.save_state();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
        mgr.sparse_set_remove(ss, 2);

        mgr.save_state();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(1));
        mgr.sparse_set_remove(ss, 1);

        mgr.save_state();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(0));

        mgr.sparse_set_remove(ss, 0);
        assert_eq!(mgr.sparse_set_get_max(ss), None);

        mgr.restore_state();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(0));
        mgr.restore_state();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(1));
        mgr.restore_state();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
    }
    #[test]
    fn get_max_is_not_affected_by_holes() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        mgr.save_state();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
        mgr.sparse_set_remove(ss, 0);

        mgr.save_state();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
        mgr.sparse_set_remove(ss, 1);

        mgr.save_state();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
        mgr.sparse_set_remove(ss, 2);

        assert_eq!(mgr.sparse_set_get_max(ss), None);

        mgr.restore_state();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
        mgr.restore_state();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
        mgr.restore_state();
        assert_eq!(mgr.sparse_set_get_max(ss), Some(2));
    }

    #[test]
    fn get_min_increases_when_lb_bumps() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        mgr.save_state();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
        mgr.sparse_set_remove(ss, 0);

        mgr.save_state();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(1));
        mgr.sparse_set_remove(ss, 1);

        mgr.save_state();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(2));

        mgr.sparse_set_remove(ss, 2);
        assert_eq!(mgr.sparse_set_get_min(ss), None);

        mgr.restore_state();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(2));
        mgr.restore_state();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(1));
        mgr.restore_state();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
    }

    #[test]
    fn get_min_is_not_affected_by_holes() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        mgr.save_state();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
        mgr.sparse_set_remove(ss, 2);

        mgr.save_state();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
        mgr.sparse_set_remove(ss, 1);

        mgr.save_state();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
        mgr.sparse_set_remove(ss, 0);

        assert_eq!(mgr.sparse_set_get_min(ss), None);

        mgr.restore_state();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
        mgr.restore_state();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
        mgr.restore_state();
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
    }

    #[test]
    fn remove_all() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(3, 0);
        assert!(!mgr.sparse_set_is_empty(ss));

        mgr.save_state();
        mgr.sparse_set_remove_all(ss);
        assert!(mgr.sparse_set_is_empty(ss));

        mgr.restore_state();
        assert!(!mgr.sparse_set_is_empty(ss));
    }

    #[test]
    fn remove_all_but() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(6, 0);
        assert_eq!(mgr.sparse_set_size(ss), 6);

        mgr.save_state();
        mgr.sparse_set_remove_all_but(ss, 3);
        assert_eq!(mgr.sparse_set_size(ss), 1);
        assert!(mgr.sparse_set_contains(ss, 3));

        mgr.restore_state();
        assert_eq!(mgr.sparse_set_size(ss), 6);
    }
    #[test]
    fn remove_all_but_wont_set_a_value_off_the_range() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(6, 0);
        assert_eq!(mgr.sparse_set_size(ss), 6);

        mgr.save_state();
        mgr.sparse_set_remove_all_but(ss, 300);
        assert_eq!(mgr.sparse_set_size(ss), 0);

        mgr.restore_state();
        assert_eq!(mgr.sparse_set_size(ss), 6);
    }

    #[test]
    fn remove() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(3, 0);

        assert!(mgr.sparse_set_contains(ss, 1));
        mgr.save_state();
        mgr.sparse_set_remove(ss, 1);
        assert!(!mgr.sparse_set_contains(ss, 1));
        mgr.restore_state();
        assert!(mgr.sparse_set_contains(ss, 1));
    }

    #[test]
    fn remove_above() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(10, 0);

        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_get_max(ss), Some(9));

        mgr.save_state();
        mgr.sparse_set_remove_above(ss, 5);
        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_get_max(ss), Some(5));

        mgr.restore_state();
        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_get_max(ss), Some(9));
    }
    #[test]
    fn remove_above_max_does_nothing() {
        let mut mgr = TrailedStateManager::new();
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
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(10, 0);

        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_size(ss), 10);
        assert_eq!(mgr.sparse_set_get_max(ss), Some(9));

        mgr.sparse_set_remove_above(ss, -1);
        assert!(mgr.sparse_set_is_empty(ss));
    }

    #[test]
    fn remove_below() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(10, 0);

        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));

        mgr.save_state();
        mgr.sparse_set_remove_below(ss, 5);
        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_get_min(ss), Some(5));

        mgr.restore_state();
        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));
    }
    #[test]
    fn remove_below_min_does_nothing() {
        let mut mgr = TrailedStateManager::new();
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
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(10, 0);

        assert!(mgr.sparse_set_contains(ss, 5));
        assert_eq!(mgr.sparse_set_size(ss), 10);
        assert_eq!(mgr.sparse_set_get_min(ss), Some(0));

        mgr.sparse_set_remove_below(ss, 10);
        assert!(mgr.sparse_set_is_empty(ss));
    }

    #[test]
    fn for_each_calls_the_function_on_each_item() {
        let mut mgr = TrailedStateManager::new();
        let ss = mgr.manage_sparse_set(5, 10);

        assert_eq!(vec![10, 11, 12, 13, 14], sorted_content(&mgr, ss));
        mgr.save_state();

        mgr.sparse_set_remove_below(ss, 12);
        assert_eq!(vec![12, 13, 14], sorted_content(&mgr, ss));
        mgr.save_state();

        mgr.sparse_set_remove(ss, 13);
        assert_eq!(vec![12, 14], sorted_content(&mgr, ss));
        mgr.save_state();

        mgr.sparse_set_remove_all(ss);
        assert_eq!(sorted_content(&mgr, ss), vec![]);

        mgr.restore_state();
        assert_eq!(vec![12, 14], sorted_content(&mgr, ss));
        mgr.restore_state();
        assert_eq!(vec![12, 13, 14], sorted_content(&mgr, ss));
        mgr.restore_state();
        assert_eq!(vec![10, 11, 12, 13, 14], sorted_content(&mgr, ss));
    }

    fn sorted_content(mgr: &TrailedStateManager, id: ReversibleSparseSet) -> Vec<isize> {
        let mut out = vec![];
        mgr.sparse_set_for_each(id, |v| out.push(v));
        out.sort_unstable();
        out
    }
}

//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~ UT INTERVAL ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#[cfg(test)]
mod tests_manager_interval {
    use super::*;

    #[test]
    fn contains_is_always_false_for_items_not_supposed_to_be_in_set() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 0);

        assert!(!mgr.interval_contains(iv, 5));
        assert!(!mgr.interval_contains(iv, 3));
        assert!(!mgr.interval_contains(iv, -3));
        assert!(!mgr.interval_contains(iv, -5));
    }

    #[test]
    fn is_empty() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 2);

        mgr.save_state();
        assert!(!mgr.interval_is_empty(iv));
        mgr.interval_remove_below(iv, 1);
        assert!(!mgr.interval_is_empty(iv));
        mgr.interval_remove_below(iv, 2);
        assert!(!mgr.interval_is_empty(iv));
        mgr.interval_remove_below(iv, 3);

        // now it is empty
        assert!(mgr.interval_is_empty(iv));
        mgr.restore_state();
        assert!(!mgr.interval_is_empty(iv));
    }

    #[test]
    fn size() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 2);

        mgr.save_state();
        assert_eq!(mgr.interval_size(iv), 3);
        mgr.interval_remove_below(iv, 1);
        assert_eq!(mgr.interval_size(iv), 2);
        mgr.interval_remove_below(iv, 2);
        assert_eq!(mgr.interval_size(iv), 1);
        mgr.interval_remove_below(iv, 3);

        // now it is empty
        assert_eq!(mgr.interval_size(iv), 0);
        mgr.restore_state();
        assert_eq!(mgr.interval_size(iv), 3);
    }

    #[test]
    fn get_max_decreases_when_ub_drops() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 2);

        mgr.save_state();
        assert_eq!(mgr.interval_get_max(iv), Some(2));
        mgr.interval_remove_above(iv, 1);

        mgr.save_state();
        assert_eq!(mgr.interval_get_max(iv), Some(1));
        mgr.interval_remove_above(iv, 0);

        mgr.save_state();
        assert_eq!(mgr.interval_get_max(iv), Some(0));

        mgr.interval_remove_above(iv, -1);
        assert_eq!(mgr.interval_get_max(iv), None);

        mgr.restore_state();
        assert_eq!(mgr.interval_get_max(iv), Some(0));
        mgr.restore_state();
        assert_eq!(mgr.interval_get_max(iv), Some(1));
        mgr.restore_state();
        assert_eq!(mgr.interval_get_max(iv), Some(2));
    }

    #[test]
    fn get_min_increases_when_lb_bumps() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 2);

        mgr.save_state();
        assert_eq!(mgr.interval_get_min(iv), Some(0));
        mgr.interval_remove_below(iv, 1);

        mgr.save_state();
        assert_eq!(mgr.interval_get_min(iv), Some(1));
        mgr.interval_remove_below(iv, 2);

        mgr.save_state();
        assert_eq!(mgr.interval_get_min(iv), Some(2));

        mgr.interval_remove_below(iv, 3);
        assert_eq!(mgr.interval_get_min(iv), None);

        mgr.restore_state();
        assert_eq!(mgr.interval_get_min(iv), Some(2));
        mgr.restore_state();
        assert_eq!(mgr.interval_get_min(iv), Some(1));
        mgr.restore_state();
        assert_eq!(mgr.interval_get_min(iv), Some(0));
    }

    #[test]
    fn remove_all() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 5);
        assert!(!mgr.interval_is_empty(iv));

        mgr.save_state();
        mgr.interval_remove_all(iv);
        assert!(mgr.interval_is_empty(iv));

        mgr.restore_state();
        assert!(!mgr.interval_is_empty(iv));
    }

    #[test]
    fn remove_all_but() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 5);
        assert_eq!(mgr.interval_size(iv), 6);

        mgr.save_state();
        mgr.interval_remove_all_but(iv, 3);
        assert_eq!(mgr.interval_size(iv), 1);
        assert!(mgr.interval_contains(iv, 3));

        mgr.restore_state();
        assert_eq!(mgr.interval_size(iv), 6);
    }

    #[test]
    fn remove_all_but_wont_set_a_value_off_the_range() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 5);
        assert_eq!(mgr.interval_size(iv), 6);

        mgr.save_state();
        mgr.interval_remove_all_but(iv, 300);
        assert_eq!(mgr.interval_size(iv), 0);

        mgr.restore_state();
        assert_eq!(mgr.interval_size(iv), 6);
    }

    #[test]
    fn remove_above() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 9);

        assert!(mgr.interval_contains(iv, 5));
        assert_eq!(mgr.interval_get_max(iv), Some(9));

        mgr.save_state();
        mgr.interval_remove_above(iv, 5);
        assert!(mgr.interval_contains(iv, 5));
        assert_eq!(mgr.interval_get_max(iv), Some(5));

        mgr.restore_state();
        assert!(mgr.interval_contains(iv, 5));
        assert_eq!(mgr.interval_get_max(iv), Some(9));
    }

    #[test]
    fn remove_above_cant_reopen_interval() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 9);

        assert!(mgr.interval_contains(iv, 5));
        assert_eq!(mgr.interval_get_max(iv), Some(9));

        mgr.save_state();
        mgr.interval_remove_below(iv, 10);
        assert!(mgr.interval_is_empty(iv));
        mgr.interval_remove_above(iv, 11);
        assert!(mgr.interval_is_empty(iv));
    }

    #[test]
    fn remove_above_max_does_nothing() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 9);

        assert!(mgr.interval_contains(iv, 5));
        assert_eq!(mgr.interval_size(iv), 10);
        assert_eq!(mgr.interval_get_max(iv), Some(9));

        mgr.interval_remove_above(iv, 10);
        assert!(mgr.interval_contains(iv, 5));
        assert_eq!(mgr.interval_size(iv), 10);
        assert_eq!(mgr.interval_get_max(iv), Some(9));
    }
    #[test]
    fn remove_above_min_empties_set() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 9);

        assert!(mgr.interval_contains(iv, 5));
        assert_eq!(mgr.interval_size(iv), 10);
        assert_eq!(mgr.interval_get_max(iv), Some(9));

        mgr.interval_remove_above(iv, -1);
        assert!(mgr.interval_is_empty(iv));
    }

    #[test]
    fn remove_below() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 5);

        assert!(mgr.interval_contains(iv, 5));
        assert_eq!(mgr.interval_get_min(iv), Some(0));

        mgr.save_state();
        mgr.interval_remove_below(iv, 5);
        assert!(mgr.interval_contains(iv, 5));
        assert_eq!(mgr.interval_get_min(iv), Some(5));

        mgr.restore_state();
        assert!(mgr.interval_contains(iv, 5));
        assert_eq!(mgr.interval_get_min(iv), Some(0));
    }
    #[test]
    fn remove_below_cant_reopen_interval() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 9);

        assert!(!mgr.interval_is_empty(iv));
        mgr.interval_remove_above(iv, -1);
        assert!(mgr.interval_is_empty(iv));
        mgr.interval_remove_below(iv, -20);
        assert!(mgr.interval_is_empty(iv));
    }
    #[test]
    fn remove_below_min_does_nothing() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 9);

        assert!(mgr.interval_contains(iv, 5));
        assert_eq!(mgr.interval_size(iv), 10);
        assert_eq!(mgr.interval_get_min(iv), Some(0));

        mgr.interval_remove_below(iv, -1);
        assert!(mgr.interval_contains(iv, 5));
        assert_eq!(mgr.interval_size(iv), 10);
        assert_eq!(mgr.interval_get_min(iv), Some(0));
    }
    #[test]
    fn remove_below_max_empties_set() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(0, 9);

        assert!(mgr.interval_contains(iv, 5));
        assert_eq!(mgr.interval_size(iv), 10);
        assert_eq!(mgr.interval_get_min(iv), Some(0));

        mgr.interval_remove_below(iv, 10);
        assert!(mgr.interval_is_empty(iv));
    }

    #[test]
    fn for_each_calls_the_function_on_each_item() {
        let mut mgr = TrailedStateManager::new();
        let iv = mgr.manage_interval(10, 14);

        assert_eq!(vec![10, 11, 12, 13, 14], sorted_content(&mgr, iv));
        mgr.save_state();

        mgr.interval_remove_below(iv, 12);
        assert_eq!(vec![12, 13, 14], sorted_content(&mgr, iv));
        mgr.save_state();

        mgr.interval_remove_all(iv);
        assert_eq!(sorted_content(&mgr, iv), vec![]);

        mgr.restore_state();
        assert_eq!(vec![12, 13, 14], sorted_content(&mgr, iv));
        mgr.restore_state();
        assert_eq!(vec![10, 11, 12, 13, 14], sorted_content(&mgr, iv));
    }

    fn sorted_content(mgr: &TrailedStateManager, id: ReversibleInterval) -> Vec<isize> {
        let mut out = vec![];
        mgr.interval_for_each(id, |v| out.push(v));
        out.sort_unstable();
        out
    }
}
