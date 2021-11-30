//! `no_std` compatibility

// Use the `std` hasher if we don’t depend on `ahash`.
#[cfg(not(feature = "ahash"))]
pub use std::collections::hash_map::RandomState;

// If we do depend on `ahash`, use its hasher.
#[cfg(feature = "ahash")]
pub use ahash::RandomState;

// If we depend on `std`, alias `lib` to `std`.
#[cfg(feature = "std")]
mod lib {
    extern crate std;
    pub use std::*;
}

// Otherwise, we are `no_std`, so alias `lib` to `alloc`.
#[cfg(not(feature = "std"))]
mod lib {
    extern crate alloc;
    pub use alloc::*;
}

// Stuff from `std`/`alloc` that we use often.
pub use lib::{
    boxed::Box,
    rc,
    slice,
    string::String,
    sync,
    vec::{self, Vec},
};

// Stuff from `core` that we use often:
pub use core::{
    borrow::Borrow,
    cmp::max,
    hash::{BuildHasher, Hash, Hasher},
    iter::{self, FromIterator},
    fmt::{self, Debug, Formatter},
    mem,
    ops::{self, Deref, Index, IndexMut},
};

// When testing, we need the `eprintln` macro from `std`:
#[cfg(test)]
extern crate std;

#[cfg(test)]
pub use std::eprintln;
