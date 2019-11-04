//! A hash set where the elements are held by weak pointers and compared by pointer.

use std::collections::hash_map::RandomState;
use std::fmt::{self, Debug};
use std::hash::BuildHasher;
use std::iter::FromIterator;
use std::ops::Deref;

use super::traits::*;
use super::ptr_weak_key_hash_map as base;
use super::by_ptr::ByPtr;

pub use super::PtrWeakHashSet;

impl <T: WeakElement> PtrWeakHashSet<T, RandomState>
    where T::Strong: Deref
{
    /// Creates an empty `PtrWeakHashSet`.
    pub fn new() -> Self {
        PtrWeakHashSet(base::PtrWeakKeyHashMap::new())
    }

    /// Creates an empty `PtrWeakHashSet` with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        PtrWeakHashSet(base::PtrWeakKeyHashMap::with_capacity(capacity))
    }
}

impl <T: WeakElement, S: BuildHasher> PtrWeakHashSet<T, S>
    where T::Strong: Deref
{
    /// Creates an empty `PtrWeakHashSet` with the given capacity and hasher.
    pub fn with_hasher(hash_builder: S) -> Self {
        PtrWeakHashSet(base::PtrWeakKeyHashMap::with_hasher(hash_builder))
    }

    /// Creates an empty `PtrWeakHashSet` with the given capacity and hasher.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        PtrWeakHashSet(base::PtrWeakKeyHashMap::with_capacity_and_hasher(capacity, hash_builder))
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

    /// Is the set known to be empty?
    ///
    /// This could answer `false` for an empty set whose elements have
    /// expired but have yet to be collected.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
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

    /// Returns true if the map contains the specified key.
    pub fn contains(&self, key: &T::Strong) -> bool {
        self.0.contains_key(key)
    }

    /// Unconditionally inserts the value, returning the old value if already present. Does not
    /// replace the key.
    pub fn insert(&mut self, key: T::Strong) -> bool {
        self.0.insert(key, ()).is_some()
    }

    /// Removes the entry with the given key, if it exists, and returns the value.
    pub fn remove(&mut self, key: &T::Strong) -> bool {
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
    pub fn is_subset<S1>(&self, other: &PtrWeakHashSet<T, S1>) -> bool
        where S1: BuildHasher
    {
        self.0.domain_is_subset(&other.0)
    }
}

/// An iterator over the elements of a set.
pub struct Iter<'a, T: 'a>(base::Keys<'a, ByPtr<T>, ()>);

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
pub struct IntoIter<T>(base::IntoIter<ByPtr<T>, ()>);

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
pub struct Drain<'a, T: 'a>(base::Drain<'a, ByPtr<T>, ()>);

impl<'a, T: WeakElement> Iterator for Drain<'a, T> {
    type Item = T::Strong;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|pair| pair.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<T: WeakElement, S> PtrWeakHashSet<T, S>
    where T::Strong: Deref
{
    /// Gets an iterator over the keys and values.
    pub fn iter(&self) -> Iter<T> {
        Iter(self.0.keys())
    }

    /// Gets a draining iterator, which removes all the values but retains the storage.
    pub fn drain(&mut self) -> Drain<T> {
        Drain(self.0.drain())
    }
}

impl<T, S, S1> PartialEq<PtrWeakHashSet<T, S1>> for PtrWeakHashSet<T, S>
    where T: WeakElement,
          T::Strong: Deref,
          S: BuildHasher,
          S1: BuildHasher
{
    fn eq(&self, other: &PtrWeakHashSet<T, S1>) -> bool {
        self.0 == other.0
    }
}

impl<T: WeakElement, S: BuildHasher> Eq for PtrWeakHashSet<T, S>
    where T::Strong: Deref
{ }

impl<T: WeakElement, S: BuildHasher + Default> Default for PtrWeakHashSet<T, S>
    where T::Strong: Deref
{
    fn default() -> Self {
        PtrWeakHashSet(base::PtrWeakKeyHashMap::<T, (), S>::default())
    }
}

impl<T, S> FromIterator<T::Strong> for PtrWeakHashSet<T, S>
    where T: WeakElement,
          T::Strong: Deref,
          S: BuildHasher + Default
{
    fn from_iter<I: IntoIterator<Item=T::Strong>>(iter: I) -> Self {
        PtrWeakHashSet(base::PtrWeakKeyHashMap::<T, (), S>::from_iter(
            iter.into_iter().map(|k| (k, ()))))
    }
}

impl<T, S> Extend<T::Strong> for PtrWeakHashSet<T, S>
    where T: WeakElement,
          T::Strong: Deref,
          S: BuildHasher
{
    fn extend<I: IntoIterator<Item=T::Strong>>(&mut self, iter: I) {
        self.0.extend(iter.into_iter().map(|k| (k, ())))
    }
}

impl<T, S> Debug for PtrWeakHashSet<T, S>
    where T: WeakElement,
          T::Strong: Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: WeakElement, S> IntoIterator for PtrWeakHashSet<T, S> {
    type Item = T::Strong;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

impl<'a, T: WeakElement, S> IntoIterator for &'a PtrWeakHashSet<T, S>
    where T::Strong: Deref
{
    type Item = T::Strong;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter(self.0.keys())
    }
}

