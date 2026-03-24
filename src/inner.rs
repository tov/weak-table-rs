//! Internal implementation for weak tables, based on [`hashbrown`].
//!
//! Rather than write our own hashtable implementation,
//! we're using `hashbrown` as a backend,
//! since it uses a lot of tricky techniques (SIMD! Swisstables!)
//! to keep performance high.
//! (It's also the backend used by Rust's standard library.)
//!
//! To avoid duplicated code,
//! we define a single [`Table`] type to serve as the backend for all of our weak tables,
//! and a pair of wrappers for [`Weak`] and [`Owned`] keys and values to hide
//! the difference between the two types.
//! These wrapper types implement internal [`Element`] and [`Key`] traits
//! that the table code uses.
//!
//! For example, a [`WeakKeyHashMap`] is internally implemented as a
//! `Table<Weak<K>, Owned<V>>`.
//!
//! [`WeakKeyHashMap`]: super::WeakKeyHashMap
mod table;
mod wrappers;

pub(crate) use table::*;
pub(crate) use wrappers::*;

/// Alias for a weak wrapper for a key.
///
/// Since this is a key, we need to store its hash.
pub(crate) type WeakK<T> = Weak<T, u64>;

/// Alias for a weak wrapper for a value.
///
/// Since this is a value, we do not need to store its hash.
pub(crate) type WeakV<T> = Weak<T, ()>;
