//! A hash set where the elements are held by weak pointers and compared by value.

use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::fmt::{self, Debug};
use std::hash::{BuildHasher, Hash};
use std::iter::FromIterator;

use super::traits::*;
use super::weak_key_hash_map as base;

pub use super::WeakHashSet;

impl <T: WeakKey> WeakHashSet<T, RandomState> {
    /// Creates an empty `WeakHashSet`.
    pub fn new() -> Self {
        WeakHashSet(base::WeakKeyHashMap::new())
    }

    /// Creates an empty `WeakHashSet` with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        WeakHashSet(base::WeakKeyHashMap::with_capacity(capacity))
    }
}

impl <T: WeakKey, S: BuildHasher> WeakHashSet<T, S> {
    /// Creates an empty `WeakHashSet` with the given capacity and hasher.
    pub fn with_hasher(hash_builder: S) -> Self {
        WeakHashSet(base::WeakKeyHashMap::with_hasher(hash_builder))
    }

    /// Creates an empty `WeakHashSet` with the given capacity and hasher.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        WeakHashSet(base::WeakKeyHashMap::with_capacity_and_hasher(capacity, hash_builder))
    }

    /// Returns a reference to the map's `BuildHasher`.
    pub fn hasher(&self) -> &S {
        self.0.hasher()
    }

    /// Returns the number of elements the map can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Removes all mappings whose keys have expired.
    pub fn remove_expired(&mut self) {
        self.0.remove_expired()
    }

    /// Reserves room for additional elements.
    pub fn reserve(&mut self, additional_capacity: usize) {
        self.0.reserve(additional_capacity)
    }

    /// Shrinks the capacity to the minimum allowed to hold the current number of elements.
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }

    /// Returns an over-approximation of the number of elements.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Is the set empty?
    ///
    /// Note that this may return false even if all keys in the set have
    /// expired, if they haven't been collected yet.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// The proportion of buckets that are used.
    ///
    /// This is an over-approximation because of expired elements.
    pub fn load_factor(&self) -> f32 {
        self.0.load_factor()
    }

    /// Removes all associations from the map.
    pub fn clear(&mut self) {
        self.0.clear()
    }

    // Non-ptr WeakHashSet should probably have `get` method.

    /// Returns true if the map contains the specified key.
    pub fn contains<Q>(&self, key: &Q) -> bool
        where Q: ?Sized + Eq + Hash,
              T::Key: Borrow<Q>
    {
        self.0.contains_key(key)
    }

    /// Gets a strong reference to the given key, if found.
    ///
    /// # Examples
    ///
    /// ```
    /// use weak_table::WeakHashSet;
    /// use std::rc::{Rc, Weak};
    /// use std::ops::Deref;
    ///
    /// let mut set: WeakHashSet<Weak<String>> = WeakHashSet::new();
    ///
    /// let a = Rc::new("a".to_owned());
    /// set.insert(a.clone());
    ///
    /// let also_a = set.get("a").unwrap();
    ///
    /// assert!(Rc::ptr_eq( &a, &also_a ));
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<T::Strong>
        where Q: ?Sized + Eq + Hash,
              T::Key: Borrow<Q>
    {
        self.0.get_key(key)
    }

    /// Unconditionally inserts the value, returning the old value if already present. Does not
    /// replace the key.
    pub fn insert(&mut self, key: T::Strong) -> bool {
        self.0.insert(key, ()).is_some()
    }

    /// Removes the entry with the given key, if it exists, and returns the value.
    pub fn remove<Q>(&mut self, key: &Q) -> bool
        where Q: ?Sized + Eq + Hash,
              T::Key: Borrow<Q>
    {
        self.0.remove(key).is_some()
    }

    /// Removes all mappings not satisfying the given predicate.
    ///
    /// Also removes any expired mappings.
    pub fn retain<F>(&mut self, mut f: F)
        where F: FnMut(T::Strong) -> bool
    {
        self.0.retain(|k, _| f(k))
    }

    /// Is self a subset of other?
    pub fn is_subset<S1>(&self, other: &WeakHashSet<T, S1>) -> bool
        where S1: BuildHasher
    {
        self.0.domain_is_subset(&other.0)
    }
}

/// An iterator over the elements of a set.
pub struct Iter<'a, T: 'a>(base::Keys<'a, T, ()>);

impl<'a, T: WeakElement> Iterator for Iter<'a, T> {
    type Item = T::Strong;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

/// An iterator over the elements of a set.
pub struct IntoIter<T>(base::IntoIter<T, ()>);

impl<T: WeakElement> Iterator for IntoIter<T> {
    type Item = T::Strong;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|pair| pair.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

/// A draining iterator over the elements of a set.
pub struct Drain<'a, T: 'a>(base::Drain<'a, T, ()>);

impl<'a, T: WeakElement> Iterator for Drain<'a, T> {
    type Item = T::Strong;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|pair| pair.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<T: WeakKey, S> WeakHashSet<T, S> {
    /// Gets an iterator over the keys and values.
    pub fn iter(&self) -> Iter<T> {
        Iter(self.0.keys())
    }

    /// Gets a draining iterator, which removes all the values but retains the storage.
    pub fn drain(&mut self) -> Drain<T> {
        Drain(self.0.drain())
    }
}

impl<T, S, S1> PartialEq<WeakHashSet<T, S1>> for WeakHashSet<T, S>
    where T: WeakKey,
          S: BuildHasher,
          S1: BuildHasher
{
    fn eq(&self, other: &WeakHashSet<T, S1>) -> bool {
        self.0 == other.0
    }
}

impl<T: WeakKey, S: BuildHasher> Eq for WeakHashSet<T, S>
    where T::Key: Eq
{ }

impl<T: WeakKey, S: BuildHasher + Default> Default for WeakHashSet<T, S> {
    fn default() -> Self {
        WeakHashSet(base::WeakKeyHashMap::<T, (), S>::default())
    }
}

impl<T, S> FromIterator<T::Strong> for WeakHashSet<T, S>
    where T: WeakKey,
          S: BuildHasher + Default
{
    fn from_iter<I: IntoIterator<Item=T::Strong>>(iter: I) -> Self {
        WeakHashSet(base::WeakKeyHashMap::<T, (), S>::from_iter(
            iter.into_iter().map(|k| (k, ()))))
    }
}

impl<T: WeakKey, S: BuildHasher> Extend<T::Strong> for WeakHashSet<T, S> {
    fn extend<I: IntoIterator<Item=T::Strong>>(&mut self, iter: I) {
        self.0.extend(iter.into_iter().map(|k| (k, ())))
    }
}

impl<T: WeakKey, S> Debug for WeakHashSet<T, S>
    where T::Strong: Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: WeakKey, S> IntoIterator for WeakHashSet<T, S> {
    type Item = T::Strong;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

impl<'a, T: WeakKey, S> IntoIterator for &'a WeakHashSet<T, S> {
    type Item = T::Strong;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter(self.0.keys())
    }
}
