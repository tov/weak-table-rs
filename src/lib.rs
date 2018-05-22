//! This library offers a variety of weak hash tables:
//!
//!   - For a hash map where the keys are held by weak pointers and compared by key value, see
//!     [`WeakKeyHashMap`](struct.WeakKeyHashMap.html).
//!
//!   - For a hash map where the keys are held by weak pointers and compared by pointer, see
//!     [`PtrWeakKeyHashMap`](struct.PtrWeakKeyHashMap.html).
//!
//!   - For a hash map where the values are held by weak pointers, see
//!     [`WeakValueHashMap`](struct.WeakValueHashMap.html).
//!
//!   - For a hash map where the keys and values are both held by weak pointers and the keys are
//!     compared by value, see
//!     [`WeakWeakHashMap`](struct.WeakWeakHashMap.html).
//!
//!   - For a hash map where the keys and values are both held by weak pointers and the keys are
//!     compared by pointer, see
//!     [`PtrWeakWeakHashMap`](struct.PtrWeakWeakHashMap.html).
//!
//!   - For a hash set where the elements are held by weak pointers and compared by element value, see
//!     [`WeakHashSet`](struct.WeakHashSet.html).
//!
//!   - For a hash set where the elements are held by weak pointers and compared by pointer, see
//!     [`PtrWeakHashSet`](struct.PtrWeakHashSet.html).
//!
//! This library supports Rust version 1.23 and later.
//!
//! # Examples
//!
//! ```
//! use weak_table::WeakHashSet;
//! use std::sync::{Arc, Weak};
//!
//! type Table = WeakHashSet<Weak<str>>;
//!
//! let mut set = Table::new();
//! let a = Arc::<str>::from("a");
//! let b = Arc::<str>::from("b");
//!
//! set.insert(a.clone());
//!
//! assert!(   set.contains("a") );
//! assert!( ! set.contains("b") );
//!
//! set.insert(b.clone());
//!
//! assert!(   set.contains("a") );
//! assert!(   set.contains("b") );
//!
//! drop(a);
//!
//! assert!( ! set.contains("a") );
//! assert!(   set.contains("b") );
//! ```

use std::collections::hash_map::RandomState;

pub mod traits;
pub mod weak_key_hash_map;
pub mod ptr_weak_key_hash_map;
pub mod weak_value_hash_map;
pub mod weak_weak_hash_map;
pub mod ptr_weak_weak_hash_map;
pub mod weak_hash_set;
pub mod ptr_weak_hash_set;

mod util;
mod by_ptr;
mod size_policy;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct HashCode(u64);

type FullBucket<K, V> = (K, V, HashCode);
type Bucket<K, V> = Option<FullBucket<K, V>>;
type TablePtr<K, V> = Box<[Bucket<K, V>]>;

/// A hash map with weak keys, hashed on key value.
///
/// When a weak pointer expires, its mapping is lazily removed.
#[derive(Clone)]
pub struct WeakKeyHashMap<K, V, S = RandomState> {
    hash_builder: S,
    inner: WeakKeyInnerMap<K, V>,
}

#[derive(Clone)]
struct WeakKeyInnerMap<K, V> {
    buckets: TablePtr<K, V>,
    len: usize,
}

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
pub struct PtrWeakKeyHashMap<K, V, S = RandomState>(
    WeakKeyHashMap<by_ptr::ByPtr<K>, V, S>
);

/// A hash map with weak values.
///
/// When a weak pointer expires, its mapping is lazily removed.
#[derive(Clone)]
pub struct WeakValueHashMap<K, V, S = RandomState> {
    hash_builder: S,
    inner: WeakValueInnerMap<K, V>,
}

#[derive(Clone)]
struct WeakValueInnerMap<K, V> {
    buckets: TablePtr<K, V>,
    len: usize,
}

/// A hash map with weak keys and weak values, hashed on key value.
///
/// When a weak pointer expires, its mapping is lazily removed.
#[derive(Clone)]
pub struct WeakWeakHashMap<K, V, S = RandomState> {
    hash_builder: S,
    inner: WeakWeakInnerMap<K, V>,
}

#[derive(Clone)]
struct WeakWeakInnerMap<K, V> {
    buckets: TablePtr<K, V>,
    len: usize,
}

/// A hash map with weak keys and weak values, hashed on key pointer.
///
/// When a weak pointer expires, its mapping is lazily removed.
#[derive(Clone)]
pub struct PtrWeakWeakHashMap<K, V, S = RandomState>(
    WeakWeakHashMap<by_ptr::ByPtr<K>, V, S>
);

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

