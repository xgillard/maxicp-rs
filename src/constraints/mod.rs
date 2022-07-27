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

//! This module provides the implementation of useful constraints. The
//! implementation of these constraint is split over in two modules. As the
//! name suggests, the 'reified' submodule provides the implementation of the
//! reified version of the constraints. The 'regular' module, on the other hand
//! provides the implenetation of the constraints that can be installed onto the
//! server but cannot be manipulated as 'conditions'.

mod plain;
mod reified;

pub use plain::*;
pub use reified::*;
