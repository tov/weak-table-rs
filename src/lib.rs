#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]

use self::compat::*;

pub mod ptr_weak_hash_set;
pub mod ptr_weak_key_hash_map;
pub mod ptr_weak_weak_hash_map;
pub mod traits;
pub mod weak_hash_set;
pub mod weak_key_hash_map;
pub mod weak_value_hash_map;
pub mod weak_weak_hash_map;

#[cfg(test)]
mod tests;

mod by_ptr;
mod compat;
mod inner;
mod macros;
mod size_policy;
mod util;

/// A hash map with weak keys, hashed on key value.
///
/// When a weak pointer expires, its mapping is lazily removed.
#[derive(Clone)]
pub struct WeakKeyHashMap<K, V, S = RandomState>(inner::Table<inner::WeakK<K>, inner::Owned<V>, S>);

/// A hash map with weak keys, hashed on key pointer.
///
/// When a weak pointer expires, its mapping is lazily removed.
///
/// # Examples
///
/// ```
/// use weak_table::PtrWeakKeyHashMap;
/// use std::rc::{Rc, Weak};
///
/// type Table = PtrWeakKeyHashMap<Weak<str>, usize>;
///
/// let mut map = Table::new();
/// let a = Rc::<str>::from("hello");
/// let b = Rc::<str>::from("hello");
///
/// map.insert(a.clone(), 5);
///
/// assert_eq!( map.get(&a), Some(&5) );
/// assert_eq!( map.get(&b), None );
///
/// map.insert(b.clone(), 7);
///
/// assert_eq!( map.get(&a), Some(&5) );
/// assert_eq!( map.get(&b), Some(&7) );
/// ```
#[derive(Clone)]
pub struct PtrWeakKeyHashMap<K, V, S = RandomState>(WeakKeyHashMap<by_ptr::ByPtr<K>, V, S>);

/// A hash map with weak values.
///
/// When a weak pointer expires, its mapping is lazily removed.
#[derive(Clone)]
pub struct WeakValueHashMap<K, V, S = RandomState>(
    inner::Table<inner::Owned<K>, inner::WeakV<V>, S>,
);

/// A hash map with weak keys and weak values, hashed on key value.
///
/// When a weak pointer expires, its mapping is lazily removed.
#[derive(Clone)]
pub struct WeakWeakHashMap<K, V, S = RandomState>(
    inner::Table<inner::WeakK<K>, inner::WeakV<V>, S>,
);

/// A hash map with weak keys and weak values, hashed on key pointer.
///
/// When a weak pointer expires, its mapping is lazily removed.
#[derive(Clone)]
pub struct PtrWeakWeakHashMap<K, V, S = RandomState>(WeakWeakHashMap<by_ptr::ByPtr<K>, V, S>);

/// A hash set with weak elements, hashed on element value.
///
/// When a weak pointer expires, its mapping is lazily removed.
#[derive(Clone)]
pub struct WeakHashSet<T, S = RandomState>(WeakKeyHashMap<T, (), S>);

/// A hash set with weak elements, hashed on element pointer.
///
/// When a weak pointer expires, its mapping is lazily removed.
#[derive(Clone)]
pub struct PtrWeakHashSet<T, S = RandomState>(PtrWeakKeyHashMap<T, (), S>);

/// An error that can occur during a `try_reserve` method.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum TryReserveError {
    /// The amount of memory that we would need to allocate
    /// would have been greater than the maximum (typically `isize::MAX).
    CapacityOverflow,

    /// We were unable to allocate memory to grow the table or set.
    AllocError {
        /// The memory layout that we were unable to allocate.
        layout: Layout,
    },
}

impl TryReserveError {
    /// Construct a TryReserveError from the hashbrown equivalent.
    ///
    /// (For implementation hiding purposes, this is not a public `From`
    /// implementation.)
    #[allow(clippy::needless_pass_by_value)]
    pub(crate) fn from_hashbrown(error: hashbrown::TryReserveError) -> Self {
        match error {
            hashbrown::TryReserveError::CapacityOverflow => TryReserveError::CapacityOverflow,
            hashbrown::TryReserveError::AllocError { layout } => {
                TryReserveError::AllocError { layout }
            }
        }
    }
}
impl Display for TryReserveError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TryReserveError::CapacityOverflow => write!(
                f,
                "Allocation failed: arithmetic overflow in capacity calculation"
            ),
            TryReserveError::AllocError { .. } => {
                write!(f, "Allocation failed: memory allocator returned an error. ")
            }
        }
    }
}
#[cfg(feature = "std")]
impl Error for TryReserveError {}
