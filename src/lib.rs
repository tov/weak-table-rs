#![doc(html_root_url = "https://docs.rs/weak-table/0.3.0")]
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
//! To add support for your own weak pointers, see
//! [the traits `WeakElement` and `WeakKey`](traits/).
//!
//! This crate supports Rust version 1.32 and later.
//!
//! # Examples
//!
//! Here we create a weak hash table mapping strings to integers.
//! Note that after dropping `one`, the key `"one"` is no longer present in the map.
//! This is because the map holds the strings as `std::sync::Weak<str>`s.
//!
//! ```
//! use weak_table::WeakKeyHashMap;
//! use std::sync::{Arc, Weak};
//!
//! let mut table = <WeakKeyHashMap<Weak<str>, u32>>::new();
//! let one = Arc::<str>::from("one");
//! let two = Arc::<str>::from("two");
//!
//! table.insert(one.clone(), 1);
//!
//! assert_eq!( table.get("one"), Some(&1) );
//! assert_eq!( table.get("two"), None );
//!
//! table.insert(two.clone(), 2);
//! *table.get_mut(&one).unwrap() += 10;
//!
//! assert_eq!( table.get("one"), Some(&11) );
//! assert_eq!( table.get("two"), Some(&2) );
//!
//! drop(one);
//!
//! assert_eq!( table.get("one"), None );
//! assert_eq!( table.get("two"), Some(&2) );
//! ```
//!
//! Here we use a weak hash set to implement a simple string interning facility:
//!
//! ```
//! use weak_table::WeakHashSet;
//! use std::ops::Deref;
//! use std::rc::{Rc, Weak};
//!
//! #[derive(Clone, Debug)]
//! pub struct Symbol(Rc<str>);
//!
//! impl PartialEq for Symbol {
//!     fn eq(&self, other: &Symbol) -> bool {
//!         Rc::ptr_eq(&self.0, &other.0)
//!     }
//! }
//!
//! impl Eq for Symbol {}
//!
//! impl Deref for Symbol {
//!     type Target = str;
//!     fn deref(&self) -> &str {
//!         &self.0
//!     }
//! }
//!
//! #[derive(Debug, Default)]
//! pub struct SymbolTable(WeakHashSet<Weak<str>>);
//!
//! impl SymbolTable {
//!     pub fn new() -> Self {
//!         Self::default()
//!     }
//!
//!     pub fn intern(&mut self, name: &str) -> Symbol {
//!         if let Some(rc) = self.0.get(name) {
//!             Symbol(rc)
//!         } else {
//!             let rc = Rc::<str>::from(name);
//!             self.0.insert(Rc::clone(&rc));
//!             Symbol(rc)
//!         }
//!     }
//! }
//!
//! #[test]
//! fn interning() {
//!     let mut tab = SymbolTable::new();
//!
//!     let a0 = tab.intern("a");
//!     let a1 = tab.intern("a");
//!     let b  = tab.intern("b");
//!
//!     assert_eq!(a0, a1);
//!     assert_ne!(a0, b);
//! }
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

