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

//! This module contains utilities that allows one to be generic over primitive
//! integer types. An alternative to defining these types would have been to
//! simply use the `num-traits` crate. This, was however decided against in
//! order to reduce the compilation time of maxicp-rs
//!

use std::{
    hash::Hash,
    ops::{Add, AddAssign, Sub, SubAssign},
};

/// This type encapsulates a primitive int
pub trait Int:
    Sized
    + Copy
    + Clone
    + Eq
    + PartialEq
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Ord
    + PartialOrd
    + Hash
    + private::Sealed // we don't want you to implement the type Int
{
    /// Returns the zero of this type
    fn zero() -> Self;
    /// Returns the one value of this type
    fn one() -> Self;
}

/// This macro generates an implementation of the Int trait for the given type $t
macro_rules! int {
    ($t: ty) => {
        impl Int for $t {
            fn zero() -> $t {
                0
            }
            fn one() -> $t {
                1
            }
        }
    };
}

// unsigned
int!(u8);
int!(u16);
int!(u32);
int!(u64);
int!(u128);
int!(usize);

// signed
int!(i8);
int!(i16);
int!(i32);
int!(i64);
int!(i128);
int!(isize);

mod private {
    /// This is a marker trait which simply cannot be implemented outside of
    /// this module which prevents anyone from implementing it. You should use
    /// this marker traits in case you want to make sure one of the traits you
    /// define is acessible but can't be implemented by any other type than
    /// the ones you thought of.
    pub trait Sealed {}

    macro_rules! sealed {
        ($t: ty) => {
            impl Sealed for $t {}
        };
    }

    // unsigned
    sealed!(u8);
    sealed!(u16);
    sealed!(u32);
    sealed!(u64);
    sealed!(u128);
    sealed!(usize);

    // signed
    sealed!(i8);
    sealed!(i16);
    sealed!(i32);
    sealed!(i64);
    sealed!(i128);
    sealed!(isize);
}
