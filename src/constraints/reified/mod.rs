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

//! This module provides the *reified* implementation of some useful constraints.

mod is_equal;
mod is_less_or_equal;
mod is_greater_or_equal;
mod is_not_equal;

pub use is_equal::*;
pub use is_less_or_equal::*;
pub use is_greater_or_equal::*;
pub use is_not_equal::*;
