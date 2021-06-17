use alloc::boxed::Box;
use alloc::vec::Vec;
pub fn new_boxed_option_slice<T>(size: usize) -> Box<[Option<T>]> {
    let mut vector = Vec::with_capacity(size);
    for _ in 0 .. size {
        vector.push(None)
    }
    vector.into_boxed_slice()
}

#[cfg(not(feature = "no_std"))]
extern crate std;
#[cfg(not(feature = "no_std"))]
pub use std::collections::hash_map::RandomState;
#[cfg(feature = "no_std")]
pub use ahash::RandomState;