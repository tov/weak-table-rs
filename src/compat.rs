//! `no_std` compatibility

// If we depend on `ahash`, use its hasher.
#[cfg(feature = "ahash")]
pub(crate) use ahash::RandomState;

// Use the `std` hasher if we don’t depend on `ahash` but do depend on
// `std`.
#[cfg(all(not(feature = "ahash"), feature = "std"))]
pub use std::collections::hash_map::RandomState;

// If we depend on neither `ahash` nor `std` then it’s an error.
#[cfg(not(any(feature = "ahash", feature = "std")))]
compile_error!("weak-table: no_std requires that you enable the `ahash` feature.");

/// If we depend on `std`, we alias `lib` to `std`.
#[cfg(feature = "std")]
mod lib {
    extern crate std;
    pub(crate) use std::*;
}

/// If we are `no_std`, we alias `lib` to `alloc`.
#[cfg(not(feature = "std"))]
mod lib {
    extern crate alloc;
    pub use alloc::*;
}

// Stuff from `std`/`alloc` that we use often.
pub(crate) use lib::{rc, sync};

#[cfg(test)]
pub(crate) use lib::{string::String, vec::Vec};

// Stuff from `core` that we use often:
pub(crate) use core::{
    borrow::Borrow,
    fmt::{self, Debug, Formatter},
    hash::{BuildHasher, Hash, Hasher},
    iter::{self, FromIterator},
    mem,
    ops::{self, Deref, Index, IndexMut},
};

// When testing, we need the `eprintln` macro from `std`:
#[cfg(test)]
extern crate std;

#[cfg(test)]
pub(crate) use std::eprintln;
