//! A hash map where the keys are held by weak pointers and compared by pointer.

use std::collections::hash_map::RandomState;
use std::fmt::{self, Debug};
use std::hash::BuildHasher;
use std::iter::FromIterator;
use std::ops::{Deref, Index, IndexMut};

use super::by_ptr::*;
use super::traits::*;
use super::weak_key_hash_map as base;

pub use super::PtrWeakKeyHashMap;
pub use super::weak_key_hash_map::{Entry, Iter, IterMut, Keys, Values, ValuesMut, Drain, IntoIter};

impl <K: WeakElement, V> PtrWeakKeyHashMap<K, V, RandomState>
    where K::Strong: Deref
{
    /// Creates an empty `PtrWeakKeyHashMap`.
    pub fn new() -> Self {
        PtrWeakKeyHashMap(base::WeakKeyHashMap::new())
    }

    /// Creates an empty `PtrWeakKeyHashMap` with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        PtrWeakKeyHashMap(base::WeakKeyHashMap::with_capacity(capacity))
    }
}

impl <K: WeakElement, V, S: BuildHasher> PtrWeakKeyHashMap<K, V, S>
    where K::Strong: Deref
{
    /// Creates an empty `PtrWeakKeyHashMap` with the given capacity and hasher.
    pub fn with_hasher(hash_builder: S) -> Self {
        PtrWeakKeyHashMap(base::WeakKeyHashMap::with_hasher(hash_builder))
    }

    /// Creates an empty `PtrWeakKeyHashMap` with the given capacity and hasher.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        PtrWeakKeyHashMap(base::WeakKeyHashMap::with_capacity_and_hasher(capacity, hash_builder))
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

    /// Is the map known to be empty?
    ///
    /// This could answer `false` for an empty map whose keys have
    /// expired but have yet to be collected.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
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
    pub fn get(&self, key: &K::Strong) -> Option<&V> {
        self.0.get(&(key.deref() as *const _))
    }

    /// Returns true if the map contains the specified key.
    pub fn contains_key(&self, key:&K::Strong) -> bool {
        self.0.contains_key(&(key.deref() as *const _))
    }

    /// Returns a mutable reference to the value corresponding to the key.
    pub fn get_mut(&mut self, key: &K::Strong) -> Option<&mut V> {
        self.0.get_mut(&(key.deref() as *const _))
    }

    /// Unconditionally inserts the value, returning the old value if already present. Does not
    /// replace the key.
    pub fn insert(&mut self, key: K::Strong, value: V) -> Option<V> {
        self.0.insert(key, value)
    }

    /// Removes the entry with the given key, if it exists, and returns the value.
    pub fn remove(&mut self, key: &K::Strong) -> Option<V> {
        self.0.remove(&(key.deref() as *const _))
    }

    /// Removes all mappings not satisfying the given predicate.
    ///
    /// Also removes any expired mappings.
    pub fn retain<F>(&mut self, f: F)
        where F: FnMut(K::Strong, &mut V) -> bool
    {
        self.0.retain(f)
    }

    /// Is this map a submap of the other, using the given value comparison.
    ///
    /// In particular, all the keys of self must be in other and the values must compare true with
    /// value_equal.
    pub fn submap_with<F, S1, V1>(&self, other: &PtrWeakKeyHashMap<K, V1, S1>, value_equal: F) -> bool
    where F: FnMut(&V, &V1) -> bool,
          S1: BuildHasher
    {
        self.0.is_submap_with(&other.0, value_equal)
    }

    /// Is self a submap of other?
    pub fn is_submap<V1, S1>(&self, other: &PtrWeakKeyHashMap<K, V1, S1>) -> bool
        where V: PartialEq<V1>,
            S1: BuildHasher
    {
        self.0.is_submap(&other.0)
    }

    /// Are the keys of self a subset of the keys of other?
    pub fn domain_is_subset<V1, S1>(&self, other: &PtrWeakKeyHashMap<K, V1, S1>) -> bool
        where S1: BuildHasher
    {
        self.0.domain_is_subset(&other.0)
    }
}

impl<K: WeakElement, V, S> PtrWeakKeyHashMap<K, V, S>
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

    /// Gets an iterator over the keys and mutable values.
    pub fn iter_mut(&mut self) -> IterMut<ByPtr<K>, V> {
        self.0.iter_mut()
    }

    /// Gets an iterator over the mutable values.
    pub fn values_mut(&mut self) -> ValuesMut<ByPtr<K>, V> {
        self.0.values_mut()
    }

    /// Gets a draining iterator, which removes all the values but retains the storage.
    pub fn drain(&mut self) -> Drain<ByPtr<K>, V> {
        self.0.drain()
    }
}

impl<K, V, V1, S, S1> PartialEq<PtrWeakKeyHashMap<K, V1, S1>>
    for PtrWeakKeyHashMap<K, V, S>
    where K: WeakElement,
          K::Strong: Deref,
          V: PartialEq<V1>,
          S: BuildHasher,
          S1: BuildHasher
{
    fn eq(&self, other: &PtrWeakKeyHashMap<K, V1, S1>) -> bool {
        self.0 == other.0
    }
}

impl<K: WeakElement, V: Eq, S: BuildHasher> Eq for PtrWeakKeyHashMap<K, V, S>
    where K::Strong: Deref
{ }

impl<K: WeakElement, V, S: BuildHasher + Default> Default for PtrWeakKeyHashMap<K, V, S>
    where K::Strong: Deref
{
    fn default() -> Self {
        PtrWeakKeyHashMap(base::WeakKeyHashMap::<ByPtr<K>, V, S>::default())
    }
}

impl<'a, K, V, S> Index<&'a K::Strong> for PtrWeakKeyHashMap<K, V, S>
    where K: WeakElement,
          K::Strong: Deref,
          S: BuildHasher
{
    type Output = V;

    fn index(&self, index: &'a K::Strong) -> &Self::Output {
        self.0.index(&(index.deref() as *const _))
    }
}

impl<'a, K, V, S> IndexMut<&'a K::Strong> for PtrWeakKeyHashMap<K, V, S>
    where
        K: WeakElement,
        K::Strong: Deref,
        S: BuildHasher
{
    fn index_mut(&mut self, index: &'a K::Strong) -> &mut Self::Output {
        self.0.index_mut(&(index.deref() as *const _))
    }
}

impl<K, V, S> FromIterator<(K::Strong, V)> for PtrWeakKeyHashMap<K, V, S>
    where K: WeakElement,
          K::Strong: Deref,
          S: BuildHasher + Default
{
    fn from_iter<T: IntoIterator<Item=(K::Strong, V)>>(iter: T) -> Self {
        PtrWeakKeyHashMap(base::WeakKeyHashMap::<ByPtr<K>, V, S>::from_iter(iter))
    }
}

impl<K, V, S> Extend<(K::Strong, V)> for PtrWeakKeyHashMap<K, V, S>
    where K: WeakElement,
          K::Strong: Deref,
          S: BuildHasher
{
    fn extend<T: IntoIterator<Item=(K::Strong, V)>>(&mut self, iter: T) {
        self.0.extend(iter)
    }
}

impl<'a, K, V, S> Extend<(&'a K::Strong, &'a V)> for PtrWeakKeyHashMap<K, V, S>
    where K: 'a + WeakElement,
          K::Strong: Clone + Deref,
          V: 'a + Clone,
          S: BuildHasher
{
    fn extend<T: IntoIterator<Item=(&'a K::Strong, &'a V)>>(&mut self, iter: T) {
        self.0.extend(iter)
    }
}

impl<K, V: Debug, S> Debug for PtrWeakKeyHashMap<K, V, S>
    where K: WeakElement,
          K::Strong: Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<K: WeakElement, V, S> IntoIterator for PtrWeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, V);
    type IntoIter = IntoIter<ByPtr<K>, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, K: WeakElement, V, S> IntoIterator for &'a PtrWeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, &'a V);
    type IntoIter = Iter<'a, ByPtr<K>, V>;

    fn into_iter(self) -> Self::IntoIter {
        (&self.0).into_iter()
    }
}

impl<'a, K: WeakElement, V, S> IntoIterator for &'a mut PtrWeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, &'a mut V);
    type IntoIter = IterMut<'a, ByPtr<K>, V>;

    fn into_iter(self) -> Self::IntoIter {
        (&mut self.0).into_iter()
    }
}

#[cfg(test)]
mod test
{
    use crate::PtrWeakKeyHashMap;
    use crate::weak_key_hash_map::Entry;
    use std::rc::{Rc, Weak};

//    fn show_me(weakmap: &PtrWeakKeyHashMap<Weak<u32>, f32>) {
//        for (key, _) in weakmap {
//            eprint!(" {:2}", *key);
//        }
//        eprintln!();
//    }

    // From https://github.com/tov/weak-table-rs/issues/1#issuecomment-461858060
    #[test]
    fn insert_and_check() {
        let mut rcs: Vec<Rc<u32>> = Vec::new();

        for i in 0 .. 200 {
            rcs.push(Rc::new(i));
        }

        let mut weakmap: PtrWeakKeyHashMap<Weak<u32>, f32> = PtrWeakKeyHashMap::new();

        for item in rcs.iter().cloned() {
            let f = *item as f32 + 0.1;
            weakmap.insert(item, f);
        }

        let mut count = 0;

        for item in &rcs {
            assert!(weakmap.contains_key(item));

            match weakmap.entry(Rc::clone(item)) {
                Entry::Occupied(_) => count += 1,
                Entry::Vacant(_) => eprintln!("PointerWeakKeyHashMap: missing: {}", *item),
            }
        }

        assert_eq!( count, rcs.len() );
    }
}
