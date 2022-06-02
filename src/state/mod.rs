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
//! the state management. Typically, this accounts for the reversible integer 
//! (stateint) and its associated trail mechanism.

use crate::utils::Int;

/// An object whose inner state can be saved and restored through the 
/// `save_state()` and `restore_state()` methods of the `StateManager`.
pub trait State {
    /// The type of the internal value of this state object
    type Inner: Sized;

    /// Retrieves the value
    fn value(&self) -> Self::Inner;

    /// Sets the value and returns the new value that was set
    fn set_value(&mut self, value: Self::Inner) -> Self::Inner;
}

/// A state object whose internal value is an integer value. Its value can be
/// respectively saved and restored through the methods `save_state()` and
/// `restore_state()` of the `StateManager`.
pub trait StateInt : State where Self::Inner: Int {
    /// Increments the value
    fn increment(&mut self) -> Self::Inner {
        self.set_value(self.value() + Self::Inner::one())
    }
    /// Decrements the value
    fn decrement(&mut self) -> Self::Inner {
        self.set_value(self.value() - Self::Inner::one())
    }
}

/// A state object whose internal value is an integer value. Its value can be
/// respectively saved and restored through the methods `save_state()` and
/// `restore_state()` of the `StateManager`.
pub trait StateBool : State<Inner = bool> {}

/// Automatically implement the StateInt trait for all types that are `State`
/// and have an `Inner` type which is an int 
impl <X> StateInt for X where X:State, X::Inner: Int {}

/// Automatically implement the StateBool trait for all types that are `State`
/// and have an `Inner` type which is a boolean 
impl <X> StateBool for X where X: State<Inner=bool> {}

/// The state manager is in charge of storing and restoring the data from 
/// and to the trail
mod manager;
pub use manager::*;