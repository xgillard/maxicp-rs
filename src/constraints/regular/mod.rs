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

//! This module provides the *not reified* implementation of some useful
//! constraints.

mod absolute;
mod equal;
mod greater_or_equal;
mod less_or_equal;
mod not_equal;

mod must_be_true;

pub use absolute::*;
pub use equal::*;
pub use greater_or_equal::*;
pub use less_or_equal::*;
pub use must_be_true::*;
pub use not_equal::*;

mod or;
pub use or::*;

mod and;
pub use and::*;