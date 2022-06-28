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

//! This module provides the implementation of the domain consistent alldiff
//! constraint. The algorithm used to implement that constraint is described
//! in "A filtering algorithm for constraints of difference in CSPs" J-C. Régin, 
//! AAAI-94.

use crate::prelude::*;

/// This constraint enforces that the the value affected to each variable be 
/// different from the one affected to all other variables. 
#[derive(Debug, Clone)]
pub struct AllDiff {
    /// All these variables must take different values in the solution
    vars: Vec<Variable>,
}
