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

/// Uniquely identifies a managed resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StateId(usize);

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
    pub fn manage(&mut self, value: T) -> StateId {
        let id = StateId(self.current.len());
        self.current.push(TrailEntry {
            id,
            clock: self.clock,
            value,
        });
        id
    }

    /// retrieves the value of the given resource
    pub fn get_value(&self, id: StateId) -> T {
        self.current[id.0].value
    }

    /// sets the value of the given resource and returns the new value of that resource
    pub fn set_value(&mut self, id: StateId, value: T) -> T {
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
    pub fn flip(&mut self, id: StateId) -> bool {
        self.set_value(id, self.get_value(id).not())
    }
}

impl<T> StateManager<T>
where
    T: Int,
{
    /// Increments the value
    pub fn increment(&mut self, id: StateId) -> T {
        self.set_value(id, self.get_value(id) + T::one())
    }
    /// Decrements the value
    pub fn decrement(&mut self, id: StateId) -> T {
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
    id: StateId,
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

// ----------------------------------------------------------------------------
// Composite manager
// ----------------------------------------------------------------------------

/// Uniquely identifies a boolean resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BoolId(StateId);
/// Uniquely identifies an unsigned (8 bits) integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct U8Id(StateId);
/// Uniquely identifies an unsigned (16 bits) integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct U16Id(StateId);
/// Uniquely identifies an unsigned (32 bits) integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct U32Id(StateId);
/// Uniquely identifies an unsigned (64 bits) integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct U64Id(StateId);
/// Uniquely identifies an unsigned (1288 bits) integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct U128Id(StateId);
/// Uniquely identifies an unsigned (platform defined) integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct USizeId(StateId);

/// Uniquely identifies a signed (8 bits) integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct I8Id(StateId);
/// Uniquely identifies a signed (16 bits) integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct I16Id(StateId);
/// Uniquely identifies a signed (32 bits) integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct I32Id(StateId);
/// Uniquely identifies a signed (64 bits) integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct I64Id(StateId);
/// Uniquely identifies a signed (128 bits) integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct I128Id(StateId);
/// Uniquely identifies a signed (platform defined) integer resource
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ISizeId(StateId);

/// A composite state manager that is capable of dealing with all
/// integral primitive types
#[derive(Debug, Default, Clone)]
pub struct CompositeStateManager {
    /// all the managed boolean data
    bool_data: StateManager<bool>,

    /// all the managed u8 data
    u8_data: StateManager<u8>,
    /// all the managed u16 data
    u16_data: StateManager<u16>,
    /// all the managed u32 data
    u32_data: StateManager<u32>,
    /// all the managed u64 data
    u64_data: StateManager<u64>,
    /// all the managed u128 data
    u128_data: StateManager<u128>,
    /// all the managed usize data
    usize_data: StateManager<usize>,

    /// all the managed i8 data
    i8_data: StateManager<i8>,
    /// all the managed i16 data
    i16_data: StateManager<i16>,
    /// all the managed i32 data
    i32_data: StateManager<i32>,
    /// all the managed i64 data
    i64_data: StateManager<i64>,
    /// all the managed i128 data
    i128_data: StateManager<i128>,
    /// all the managed isize data
    isize_data: StateManager<isize>,
}

impl CompositeStateManager {
    /// Creates a new composite state manager
    pub fn new() -> Self {
        Default::default()
    }

    /// Saves the current state
    pub fn push(&mut self) {
        self.bool_data.push();

        self.u8_data.push();
        self.u16_data.push();
        self.u32_data.push();
        self.u64_data.push();
        self.u128_data.push();
        self.usize_data.push();

        self.i8_data.push();
        self.i16_data.push();
        self.i32_data.push();
        self.i64_data.push();
        self.i128_data.push();
        self.isize_data.push();
    }

    /// Restores the previous state
    pub fn pop(&mut self) {
        self.bool_data.pop();

        self.u8_data.pop();
        self.u16_data.pop();
        self.u32_data.pop();
        self.u64_data.pop();
        self.u128_data.pop();
        self.usize_data.pop();

        self.i8_data.pop();
        self.i16_data.pop();
        self.i32_data.pop();
        self.i64_data.pop();
        self.i128_data.pop();
        self.isize_data.pop();
    }

    /// Creates a new managed bool resource
    pub fn manage_bool(&mut self, value: bool) -> BoolId {
        BoolId(self.bool_data.manage(value))
    }
    /// Gets a boolean value
    pub fn get_bool(&self, id: BoolId) -> bool {
        self.bool_data.get_value(id.0)
    }
    /// Sets a boolean value and returns it
    pub fn set_bool(&mut self, id: BoolId, value: bool) -> bool {
        self.bool_data.set_value(id.0, value)
    }
    /// Flips a boolean value and returns the new value
    pub fn flip_bool(&mut self, id: BoolId) -> bool {
        self.bool_data.flip(id.0)
    }

    /// Creates a new managed unsigned (8 bits) resource
    pub fn manage_u8(&mut self, value: bool) -> BoolId {
        BoolId(self.bool_data.manage(value))
    }
    /// Gets am unsigned integer value
    pub fn get_u8(&self, id: U8Id) -> u8 {
        self.u8_data.get_value(id.0)
    }
    /// Sets an unsigned integer value and returns it
    pub fn set_u8(&mut self, id: U8Id, value: u8) -> u8 {
        self.u8_data.set_value(id.0, value)
    }
    /// Increments an unsigned integer value and returns the new value
    pub fn increment_u8(&mut self, id: U8Id) -> u8 {
        self.u8_data.increment(id.0)
    }
    /// Decrements an unsigned integer value and returns the new value
    pub fn decrement_u8(&mut self, id: U8Id) -> u8 {
        self.u8_data.decrement(id.0)
    }

    /// Creates a new managed unsigned integer (16 bits) resource
    pub fn manage_u16(&mut self, value: bool) -> BoolId {
        BoolId(self.bool_data.manage(value))
    }
    /// Gets am unsigned integer value
    pub fn get_u16(&self, id: U16Id) -> u16 {
        self.u16_data.get_value(id.0)
    }
    /// Sets an unsigned integer value and returns it
    pub fn set_u16(&mut self, id: U16Id, value: u16) -> u16 {
        self.u16_data.set_value(id.0, value)
    }
    /// Increments an unsigned integer value and returns the new value
    pub fn increment_u16(&mut self, id: U16Id) -> u16 {
        self.u16_data.increment(id.0)
    }
    /// Decrements an unsigned integer value and returns the new value
    pub fn decrement_u16(&mut self, id: U16Id) -> u16 {
        self.u16_data.decrement(id.0)
    }

    /// Creates a new managed unsigned integer (32 bits) resource
    pub fn manage_u32(&mut self, value: bool) -> BoolId {
        BoolId(self.bool_data.manage(value))
    }
    /// Gets am unsigned integer value
    pub fn get_u32(&self, id: U32Id) -> u32 {
        self.u32_data.get_value(id.0)
    }
    /// Sets an unsigned integer value and returns it
    pub fn set_u32(&mut self, id: U32Id, value: u32) -> u32 {
        self.u32_data.set_value(id.0, value)
    }
    /// Increments an unsigned integer value and returns the new value
    pub fn increment_u32(&mut self, id: U32Id) -> u32 {
        self.u32_data.increment(id.0)
    }
    /// Decrements an unsigned integer value and returns the new value
    pub fn decrement_u32(&mut self, id: U32Id) -> u32 {
        self.u32_data.decrement(id.0)
    }

    /// Creates a new managed unsigned integer (64 bits) resource
    pub fn manage_u64(&mut self, value: bool) -> BoolId {
        BoolId(self.bool_data.manage(value))
    }
    /// Gets am unsigned integer value
    pub fn get_u64(&self, id: U64Id) -> u64 {
        self.u64_data.get_value(id.0)
    }
    /// Sets an unsigned integer value and returns it
    pub fn set_u64(&mut self, id: U64Id, value: u64) -> u64 {
        self.u64_data.set_value(id.0, value)
    }
    /// Increments an unsigned integer value and returns the new value
    pub fn increment_u64(&mut self, id: U64Id) -> u64 {
        self.u64_data.increment(id.0)
    }
    /// Decrements an unsigned integer value and returns the new value
    pub fn decrement_u64(&mut self, id: U64Id) -> u64 {
        self.u64_data.decrement(id.0)
    }

    /// Creates a new managed unsigned integer (128 bits) resource
    pub fn manage_u128(&mut self, value: bool) -> BoolId {
        BoolId(self.bool_data.manage(value))
    }
    /// Gets am unsigned integer value
    pub fn get_u128(&self, id: U128Id) -> u128 {
        self.u128_data.get_value(id.0)
    }
    /// Sets an unsigned integer value and returns it
    pub fn set_u128(&mut self, id: U128Id, value: u128) -> u128 {
        self.u128_data.set_value(id.0, value)
    }
    /// Increments an unsigned integer value and returns the new value
    pub fn increment_u128(&mut self, id: U128Id) -> u128 {
        self.u128_data.increment(id.0)
    }
    /// Decrements an unsigned integer value and returns the new value
    pub fn decrement_u128(&mut self, id: U128Id) -> u128 {
        self.u128_data.decrement(id.0)
    }

    /// Creates a new managed unsigned integer (size bits) resource
    pub fn manage_usize(&mut self, value: bool) -> BoolId {
        BoolId(self.bool_data.manage(value))
    }
    /// Gets am unsigned integer value
    pub fn get_usize(&self, id: USizeId) -> usize {
        self.usize_data.get_value(id.0)
    }
    /// Sets an unsigned integer value and returns it
    pub fn set_usize(&mut self, id: USizeId, value: usize) -> usize {
        self.usize_data.set_value(id.0, value)
    }
    /// Increments an unsigned integer value and returns the new value
    pub fn increment_usize(&mut self, id: USizeId) -> usize {
        self.usize_data.increment(id.0)
    }
    /// Decrements an unsigned integer value and returns the new value
    pub fn decrement_usize(&mut self, id: USizeId) -> usize {
        self.usize_data.decrement(id.0)
    }

    /// Creates a new managed unsigned (8 bits) resource
    pub fn manage_i8(&mut self, value: bool) -> BoolId {
        BoolId(self.bool_data.manage(value))
    }
    /// Gets am unsigned integer value
    pub fn get_i8(&self, id: I8Id) -> i8 {
        self.i8_data.get_value(id.0)
    }
    /// Sets an unsigned integer value and returns it
    pub fn set_i8(&mut self, id: I8Id, value: i8) -> i8 {
        self.i8_data.set_value(id.0, value)
    }
    /// Increments an unsigned integer value and returns the new value
    pub fn increment_i8(&mut self, id: I8Id) -> i8 {
        self.i8_data.increment(id.0)
    }
    /// Decrements an unsigned integer value and returns the new value
    pub fn decrement_i8(&mut self, id: I8Id) -> i8 {
        self.i8_data.decrement(id.0)
    }

    /// Creates a new managed unsigned integer (16 bits) resource
    pub fn manage_i16(&mut self, value: bool) -> BoolId {
        BoolId(self.bool_data.manage(value))
    }
    /// Gets am unsigned integer value
    pub fn get_i16(&self, id: I16Id) -> i16 {
        self.i16_data.get_value(id.0)
    }
    /// Sets an unsigned integer value and returns it
    pub fn set_i16(&mut self, id: I16Id, value: i16) -> i16 {
        self.i16_data.set_value(id.0, value)
    }
    /// Increments an unsigned integer value and returns the new value
    pub fn increment_i16(&mut self, id: I16Id) -> i16 {
        self.i16_data.increment(id.0)
    }
    /// Decrements an unsigned integer value and returns the new value
    pub fn decrement_i16(&mut self, id: I16Id) -> i16 {
        self.i16_data.decrement(id.0)
    }

    /// Creates a new managed unsigned integer (32 bits) resource
    pub fn manage_i32(&mut self, value: bool) -> BoolId {
        BoolId(self.bool_data.manage(value))
    }
    /// Gets am unsigned integer value
    pub fn get_i32(&self, id: I32Id) -> i32 {
        self.i32_data.get_value(id.0)
    }
    /// Sets an unsigned integer value and returns it
    pub fn set_i32(&mut self, id: I32Id, value: i32) -> i32 {
        self.i32_data.set_value(id.0, value)
    }
    /// Increments an unsigned integer value and returns the new value
    pub fn increment_i32(&mut self, id: I32Id) -> i32 {
        self.i32_data.increment(id.0)
    }
    /// Decrements an unsigned integer value and returns the new value
    pub fn decrement_i32(&mut self, id: I32Id) -> i32 {
        self.i32_data.decrement(id.0)
    }

    /// Creates a new managed unsigned integer (64 bits) resource
    pub fn manage_i64(&mut self, value: bool) -> BoolId {
        BoolId(self.bool_data.manage(value))
    }
    /// Gets am unsigned integer value
    pub fn get_i64(&self, id: I64Id) -> i64 {
        self.i64_data.get_value(id.0)
    }
    /// Sets an unsigned integer value and returns it
    pub fn set_i64(&mut self, id: I64Id, value: i64) -> i64 {
        self.i64_data.set_value(id.0, value)
    }
    /// Increments an unsigned integer value and returns the new value
    pub fn increment_i64(&mut self, id: I64Id) -> i64 {
        self.i64_data.increment(id.0)
    }
    /// Decrements an unsigned integer value and returns the new value
    pub fn decrement_i64(&mut self, id: I64Id) -> i64 {
        self.i64_data.decrement(id.0)
    }

    /// Creates a new managed unsigned integer (128 bits) resource
    pub fn manage_i128(&mut self, value: bool) -> BoolId {
        BoolId(self.bool_data.manage(value))
    }
    /// Gets am unsigned integer value
    pub fn get_i128(&self, id: I128Id) -> i128 {
        self.i128_data.get_value(id.0)
    }
    /// Sets an unsigned integer value and returns it
    pub fn set_i128(&mut self, id: I128Id, value: i128) -> i128 {
        self.i128_data.set_value(id.0, value)
    }
    /// Increments an unsigned integer value and returns the new value
    pub fn increment_i128(&mut self, id: I128Id) -> i128 {
        self.i128_data.increment(id.0)
    }
    /// Decrements an unsigned integer value and returns the new value
    pub fn decrement_i128(&mut self, id: I128Id) -> i128 {
        self.i128_data.decrement(id.0)
    }

    /// Creates a new managed unsigned integer (size bits) resource
    pub fn manage_isize(&mut self, value: bool) -> BoolId {
        BoolId(self.bool_data.manage(value))
    }
    /// Gets am unsigned integer value
    pub fn get_isize(&self, id: ISizeId) -> isize {
        self.isize_data.get_value(id.0)
    }
    /// Sets an unsigned integer value and returns it
    pub fn set_isize(&mut self, id: ISizeId, value: isize) -> isize {
        self.isize_data.set_value(id.0, value)
    }
    /// Increments an unsigned integer value and returns the new value
    pub fn increment_isize(&mut self, id: ISizeId) -> isize {
        self.isize_data.increment(id.0)
    }
    /// Decrements an unsigned integer value and returns the new value
    pub fn decrement_isize(&mut self, id: ISizeId) -> isize {
        self.isize_data.decrement(id.0)
    }
}

#[cfg(test)]
mod tests {
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
