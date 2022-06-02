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

/// The state manager is in charge of storing and restoring the data from
/// and to the trail
mod manager;
pub use manager::*;

