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
#[derive(Debug, Clone, Copy)]
pub struct StateId(usize);

/// This is the structure which is in charge of guaranteeing that all data 
/// are properly saved and restored as though they were pushed on a stack
#[derive(Debug, Clone, Default)]
pub struct StateManager<T> where T: Eq + Copy {
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
    trail  : Vec<TrailEntry<T>>,
    /// The various 'levels' of data that have been 'push' and 'pop' separated
    levels : Vec<Level>,
}

impl <T> StateManager<T> where T: Eq + Copy {
    /// creates a new empty state manager
    pub fn new() -> Self {
        Self {
            clock  : 0,
            current: vec![],
            trail  : vec![],
            levels : vec![Level{trail_size: 0, accessible: 0}],
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
        self.levels.push(Level{
            trail_size: self.trail.len(), 
            accessible: self.current.len()
        })
    }

    /// restore the current state
    pub fn pop(&mut self) {
        let level = self.levels.pop().expect("cannot pop above the root level of the state manager");
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

impl <T> StateManager<T> where T: Int {
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
struct TrailEntry<T> where T: Eq + Copy {
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
        
        let a = mgr.manage( 10);
        assert_eq!(mgr.get_value(a), 10);

        mgr.push();
        let b = mgr.manage( 20);

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