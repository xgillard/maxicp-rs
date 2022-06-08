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

//! # MaxiCP-rs
//!
//! This project aims at implementing a fast, and clean constraint programming
//! solver with a focus on correctness, simplicity, maintainability and
//! performance. It is largely inspired by both minicp <https://www.minicp.org> and
//! maxicp <https://pschaus.github.io/maxicp/>.
//!

pub mod state;
pub mod engine;

mod prelude;
pub use prelude::*;
