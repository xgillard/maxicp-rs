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

//! This module provides the implementation of some useful constraints.

mod absolute;
mod equal;
mod is_equal;
mod not_equal;
mod less_or_equal;
mod greater_or_equal;

pub use absolute::*;
pub use equal::*;
pub use is_equal::*;
pub use not_equal::*;
pub use less_or_equal::*;
pub use greater_or_equal::*;