//! A hash map where the keys and values are both held by weak pointers, and keys are compared by
//! pointer.

use std::collections::hash_map::RandomState;
use std::fmt::{self, Debug};
use std::hash::BuildHasher;
use std::iter::FromIterator;
use std::ops::Deref;

use super::by_ptr::*;
use super::traits::*;
use super::weak_weak_hash_map as base;

pub use super::PtrWeakWeakHashMap;
pub use super::weak_weak_hash_map::{Entry, Iter, Keys, Values, Drain, IntoIter};

impl <K: WeakElement, V: WeakElement> PtrWeakWeakHashMap<K, V, RandomState>
    where K::Strong: Deref
{
    /// Creates an empty `PtrWeakWeakHashMap`.
    pub fn new() -> Self {
        PtrWeakWeakHashMap(base::WeakWeakHashMap::new())
    }

    /// Creates an empty `PtrWeakWeakHashMap` with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        PtrWeakWeakHashMap(base::WeakWeakHashMap::with_capacity(capacity))
    }
}

impl <K: WeakElement, V: WeakElement, S: BuildHasher> PtrWeakWeakHashMap<K, V, S>
    where K::Strong: Deref
{
    /// Creates an empty `PtrWeakWeakHashMap` with the given capacity and hasher.
    pub fn with_hasher(hash_builder: S) -> Self {
        PtrWeakWeakHashMap(base::WeakWeakHashMap::with_hasher(hash_builder))
    }

    /// Creates an empty `PtrWeakWeakHashMap` with the given capacity and hasher.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        PtrWeakWeakHashMap(base::WeakWeakHashMap::with_capacity_and_hasher(capacity, hash_builder))
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

    /// Is the map empty?
    ///
    /// Note that this may return false even if all keys in the map have
    /// expired, if they haven't been collected yet.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// The proportion of buckets that are used.
    ///
    /// This is an over-approximation because of expired keys.
    pub fn load_factor(&self) -> f32 {
        self.0.load_factor()
    }

    /// Gets the requested entry.
    pub fn entry(&mut self, key: K::Strong) -> Entry<ByPtr<K>, V> {
        self.0.entry(key)
    }

    /// Removes all associations from the map.
    pub fn clear(&mut self) {
        self.0.clear()
    }

    /// Returns a reference to the value corresponding to the key.
    pub fn get(&self, key: &K::Strong) -> Option<V::Strong> {
        self.0.get(&(key.deref() as *const _))
    }

    /// Returns true if the map contains the specified key.
    pub fn contains_key(&self, key: &K::Strong) -> bool {
        self.0.contains_key(&(key.deref() as *const _))
    }

    /// Unconditionally inserts the value, returning the old value if already present. Does not
    /// replace the key.
    pub fn insert(&mut self, key: K::Strong, value: V::Strong) -> Option<V::Strong> {
        self.0.insert(key, value)
    }

    /// Removes the entry with the given key, if it exists, and returns the value.
    pub fn remove(&mut self, key: &K::Strong) -> Option<V::Strong> {
        self.0.remove(&(key.deref() as *const _))
    }

    /// Removes all mappings not satisfying the given predicate.
    ///
    /// Also removes any expired mappings.
    pub fn retain<F>(&mut self, f: F)
        where F: FnMut(K::Strong, V::Strong) -> bool
    {
        self.0.retain(f)
    }

    /// Is this map a submap of the other, using the given value comparison.
    ///
    /// In particular, all the keys of self must be in other and the values must compare true with
    /// value_equal.
    pub fn submap_with<F, S1, V1>(&self, other: &PtrWeakWeakHashMap<K, V1, S1>, value_equal: F) -> bool
    where F: FnMut(V::Strong, V1::Strong) -> bool,
          V1: WeakElement,
          S1: BuildHasher
    {
        self.0.is_submap_with(&other.0, value_equal)
    }

    /// Is self a submap of other?
    pub fn is_submap<V1, S1>(&self, other: &PtrWeakWeakHashMap<K, V1, S1>) -> bool
        where V1: WeakElement,
              V::Strong: PartialEq<V1::Strong>,
              S1: BuildHasher
    {
        self.0.is_submap(&other.0)
    }

    /// Are the keys of self a subset of the keys of other?
    pub fn domain_is_subset<V1, S1>(&self, other: &PtrWeakWeakHashMap<K, V1, S1>) -> bool
        where V1: WeakElement,
              S1: BuildHasher
    {
        self.0.domain_is_subset(&other.0)
    }
}

impl<K: WeakElement, V: WeakElement, S> PtrWeakWeakHashMap<K, V, S>
    where K::Strong: Deref
{
    /// Gets an iterator over the keys and values.
    pub fn iter(&self) -> Iter<ByPtr<K>, V> {
        self.0.iter()
    }

    /// Gets an iterator over the keys.
    pub fn keys(&self) -> Keys<ByPtr<K>, V> {
        self.0.keys()
    }

    /// Gets an iterator over the values.
    pub fn values(&self) -> Values<ByPtr<K>, V> {
        self.0.values()
    }

    /// Gets a draining iterator, which removes all the values but retains the storage.
    pub fn drain(&mut self) -> Drain<ByPtr<K>, V> {
        self.0.drain()
    }
}

impl<K, V, V1, S, S1> PartialEq<PtrWeakWeakHashMap<K, V1, S1>>
    for PtrWeakWeakHashMap<K, V, S>
    where K: WeakElement,
          K::Strong: Deref,
          V: WeakElement,
          V1: WeakElement,
          V::Strong: PartialEq<V1::Strong>,
          S: BuildHasher,
          S1: BuildHasher
{
    fn eq(&self, other: &PtrWeakWeakHashMap<K, V1, S1>) -> bool {
        self.0 == other.0
    }
}

impl<K: WeakElement, V: WeakElement, S: BuildHasher> Eq for PtrWeakWeakHashMap<K, V, S>
    where K::Strong: Deref,
          V::Strong: Eq
{ }

impl<K: WeakElement, V: WeakElement, S: BuildHasher + Default> Default for PtrWeakWeakHashMap<K, V, S>
    where K::Strong: Deref
{
    fn default() -> Self {
        PtrWeakWeakHashMap(base::WeakWeakHashMap::<ByPtr<K>, V, S>::default())
    }
}

impl<K, V, S> FromIterator<(K::Strong, V::Strong)> for PtrWeakWeakHashMap<K, V, S>
    where K: WeakElement,
          K::Strong: Deref,
          V: WeakElement,
          S: BuildHasher + Default
{
    fn from_iter<T: IntoIterator<Item=(K::Strong, V::Strong)>>(iter: T) -> Self {
        PtrWeakWeakHashMap(base::WeakWeakHashMap::<ByPtr<K>, V, S>::from_iter(iter))
    }
}

impl<K, V, S> Extend<(K::Strong, V::Strong)> for PtrWeakWeakHashMap<K, V, S>
    where K: WeakElement,
          K::Strong: Deref,
          V: WeakElement,
          S: BuildHasher
{
    fn extend<T: IntoIterator<Item=(K::Strong, V::Strong)>>(&mut self, iter: T) {
        self.0.extend(iter)
    }
}

impl<K, V, S> Debug for PtrWeakWeakHashMap<K, V, S>
    where K: WeakElement,
          K::Strong: Debug,
          V: WeakElement,
          V::Strong: Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<K: WeakElement, V: WeakElement, S> IntoIterator for PtrWeakWeakHashMap<K, V, S> {
    type Item = (K::Strong, V::Strong);
    type IntoIter = IntoIter<ByPtr<K>, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, K: WeakElement, V: WeakElement, S> IntoIterator for &'a PtrWeakWeakHashMap<K, V, S> {
    type Item = (K::Strong, V::Strong);
    type IntoIter = Iter<'a, ByPtr<K>, V>;

    fn into_iter(self) -> Self::IntoIter {
        (&self.0).into_iter()
    }
}

#[cfg(test)]
mod test
{
    use crate::PtrWeakWeakHashMap;
    use crate::weak_weak_hash_map::Entry;
    use std::rc::{Rc, Weak};

//    fn show_me(weakmap: &PtrWeakWeakHashMap<Weak<u32>, Weak<f32>>) {
//        for (key, _) in weakmap {
//            eprint!(" {:2}", *key);
//        }
//        eprintln!();
//    }

    // From https://github.com/tov/weak-table-rs/issues/1#issuecomment-461858060
    #[test]
    fn insert_and_check() {
        let mut rcs: Vec<(Rc<u32>, Rc<f32>)> = Vec::new();

        for i in 0 .. 200 {
            rcs.push((Rc::new(i), Rc::new(i as f32 + 0.1)));
        }

        let mut weakmap: PtrWeakWeakHashMap<Weak<u32>, Weak<f32>> = PtrWeakWeakHashMap::new();

        for (key, value) in rcs.iter().cloned() {
            weakmap.insert(key, value);
//            show_me(&weakmap);
        }

        let mut count = 0;

        for (key, value) in &rcs {
            assert!(weakmap.contains_key(key));

            match weakmap.entry(Rc::clone(key)) {
                Entry::Occupied(occ) => {
                    assert_eq!( occ.get(), value );
                    count += 1;
                }
                Entry::Vacant(_) => {
                    eprintln!("PointerWeakWeakHashMap: missing: {}", *key);
                }
            }
        }

        assert_eq!( count, rcs.len() );
    }
}


