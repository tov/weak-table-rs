//! A hash map where the values are held by weak pointers.

use crate::macros::*;

use super::size_policy::*;
use super::traits::*;
use super::*;

pub use super::WeakValueHashMap;

/// Represents an entry in the table which may be occupied or vacant.
#[allow(clippy::exhaustive_enums)]
pub enum Entry<'a, K: 'a, V: 'a + WeakElement> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K, V>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, K, V>),
}

/// An occupied entry, which can be removed, modified, or viewed.
pub struct OccupiedEntry<'a, K: 'a, V: 'a + WeakElement>(
    inner::OccupiedEntry<'a, inner::Owned<K>, inner::WeakV<V>>,
);

/// A vacant entry, which can be inserted in or viewed.
pub struct VacantEntry<'a, K: 'a, V: 'a + WeakElement>(
    inner::VacantEntry<'a, inner::Owned<K>, inner::WeakV<V>>,
);

/// An iterator over the keys and values of the weak hash map.
#[derive(Clone, Debug)]
pub struct Iter<'a, K: 'a, V: 'a>(inner::Iter<'a, inner::Owned<K>, inner::WeakV<V>>);

impl<'a, K, V: WeakElement> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, V::Strong);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

/// An iterator over the keys of the weak hash map.
#[derive(Clone, Debug)]
pub struct Keys<'a, K: 'a, V: 'a>(Iter<'a, K, V>);

impl<'a, K, V: WeakElement> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

/// An iterator over the values of the weak hash map.
#[derive(Clone, Debug)]
pub struct Values<'a, K: 'a, V: 'a>(Iter<'a, K, V>);

impl<'a, K, V: WeakElement> Iterator for Values<'a, K, V> {
    type Item = V::Strong;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

#[derive(Debug)]
/// An iterator that consumes the values of a weak hash map, leaving it empty.
///
/// Once this iterator is dropped, all values are removed from the map,
/// whether the iterator itself was drained or not.
pub struct Drain<'a, K: 'a, V: 'a>(inner::Drain<'a, inner::Owned<K>, inner::WeakV<V>>);

impl<'a, K, V: WeakElement> Iterator for Drain<'a, K, V> {
    type Item = (K, V::Strong);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

/// An iterator that consumes a weak hash map, leaving it empty.
pub struct IntoIter<K, V>(inner::IntoIter<inner::Owned<K>, inner::WeakV<V>>);

impl<K, V: WeakElement> Iterator for IntoIter<K, V> {
    type Item = (K, V::Strong);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

into_kv_types!(K, V::Strong where {V: WeakElement});

impl<K: Eq + Hash, V: WeakElement> WeakValueHashMap<K, V, RandomState> {
    /// Creates an empty `WeakValueHashMap`.
    ///
    /// *O*(1) time
    pub fn new() -> Self {
        Self::with_capacity(DEFAULT_INITIAL_CAPACITY)
    }

    /// Creates an empty `WeakValueHashMap` with the given capacity.
    ///
    /// *O*(*n*) time
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, Default::default())
    }
}

impl<K: Eq + Hash, V: WeakElement, S: BuildHasher> WeakValueHashMap<K, V, S> {
    /// Creates an empty `WeakValueHashMap` with the given hasher.
    ///
    /// *O*(*n*) time
    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_capacity_and_hasher(DEFAULT_INITIAL_CAPACITY, hash_builder)
    }

    /// Creates an empty `WeakValueHashMap` with the given capacity and hasher.
    ///
    /// *O*(*n*) time
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        WeakValueHashMap(inner::Table::new(capacity, hash_builder))
    }

    /// Returns a reference to the map's `BuildHasher`.
    ///
    /// *O*(1) time
    pub fn hasher(&self) -> &S {
        self.0.hasher()
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// *O*(1) time
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Removes all mappings whose keys have expired.
    ///
    /// *O*(*n*) time
    pub fn remove_expired(&mut self) {
        self.0.remove_expired();
    }

    /// Reserves room for additional elements.
    ///
    /// This method ensures that at least `additional_capacity` insertions
    /// may be performed without reallocating.
    ///
    /// *O*(*n*) time
    pub fn reserve(&mut self, additional_capacity: usize) {
        self.try_reserve(additional_capacity)
            .expect("Unable to reserve additional capacity");
    }

    /// Tries to reserve room for additional elements.
    ///
    /// If this method succeeds, then at least `additional_capacity` insertions
    /// may be performed without reallocating further.
    ///
    /// *O*(*n*) time
    pub fn try_reserve(
        &mut self,
        additional_capacity: usize,
    ) -> Result<(), crate::TryReserveError> {
        self.0.try_reserve(additional_capacity)
    }

    /// Shrinks the capacity to the minimum allowed to hold the current number of elements.
    ///
    /// *O*(*n*) time
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit();
    }

    /// Shrinks capacity to hold no fewer than `min_capacity` elements.
    ///
    /// May remove expired items if necessary.
    /// Does nothing if the current capacity is already at `min_capacity` or below.
    ///
    /// *O*(*n*) time
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.0.shrink_to(min_capacity);
    }

    /// Returns an over-approximation of the number of elements.
    ///
    /// (This is an over-approximation because it includes expired elements.)
    ///
    /// (This is an over-approximation because it includes expired elements.)
    ///    /// *O*(1) time
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Is the map empty?
    ///
    /// Note that this may return false even if all keys in the map have
    /// expired, if they haven't been collected yet.
    ///
    /// *O*(1) time
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The proportion of buckets that are used.
    ///
    /// This is an over-approximation because of expired keys.
    ///
    /// *O*(1) time
    pub fn load_factor(&self) -> f32 {
        self.0.load_factor()
    }

    /// Gets the requested entry.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        match self.0.entry(key) {
            inner::Entry::Occupied(occupied) => Entry::Occupied(OccupiedEntry(occupied)),
            inner::Entry::Vacant(vacant) => Entry::Vacant(VacantEntry(vacant)),
        }
    }

    /// Removes all associations from the map.
    ///
    /// *O*(*n*) time
    pub fn clear(&mut self) {
        self.0.clear();
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// Returns `None` if no matching key is found.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn get<Q>(&self, key: &Q) -> Option<V::Strong>
    where
        Q: ?Sized + Hash + Eq,
        K: Borrow<Q>,
    {
        Some(self.0.find(key)?.1)
    }

    /// Returns true if the map contains the specified key.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        Q: ?Sized + Hash + Eq,
        K: Borrow<Q>,
    {
        self.0.find(key).is_some()
    }

    /// Unconditionally inserts the value, returning the old value if already present.
    ///
    /// Like `std::collections::HashMap`, this does not replace the key if occupied.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn insert(&mut self, key: K, value: V::Strong) -> Option<V::Strong> {
        match self.entry(key) {
            Entry::Occupied(mut occupied) => Some(occupied.insert(value)),
            Entry::Vacant(vacant) => {
                vacant.insert(value);
                None
            }
        }
    }

    /// Removes the entry with the given key, if it exists, and returns the value.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V::Strong>
    where
        Q: ?Sized + Hash + Eq,
        K: Borrow<Q>,
    {
        self.0.find_entry(key).map(|occupied| occupied.remove().1)
    }

    /// Removes the entry with the given key, if it exists, and returns both the
    /// key and value.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K, V::Strong)>
    where
        Q: ?Sized + Hash + Eq,
        K: Borrow<Q>,
    {
        Some(self.0.find_entry(key)?.remove())
    }

    /// Removes all mappings not satisfying the given predicate.
    ///
    /// Also removes any expired mappings.
    ///
    /// *O*(*n*) time
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, V::Strong) -> bool,
    {
        // TODO: It would be better to use a retain method on Table, but I've
        // run into lifetime issues there. See "TODO retain" in inner/table.rs
        self.0.table.retain(|(k, v)| {
            if let Some(v) = v.val.view() {
                f(&k.val, v)
            } else {
                false
            }
        });
    }

    /// Is this map a submap of the other, using the given value comparison.
    ///
    /// In particular, all the keys of `self` must be in `other` and the values must compare
    /// `true` with `value_equal`.
    ///
    /// expected *O*(*n*) time; worst-case *O*(*nq*) time (where *n* is
    /// `self.capacity()` and *q* is the length of the probe sequences
    /// in `other`)
    pub fn is_submap_with<F, S1, V1>(
        &self,
        other: &WeakValueHashMap<K, V1, S1>,
        mut value_equal: F,
    ) -> bool
    where
        V1: WeakElement,
        F: FnMut(V::Strong, V1::Strong) -> bool,
        S1: BuildHasher,
    {
        for (key, value1) in self {
            if let Some(value2) = other.get(key) {
                if !value_equal(value1, value2) {
                    return false;
                }
            } else {
                return false;
            }
        }

        true
    }

    /// Is `self` a submap of `other`?
    ///
    /// expected *O*(*n*) time; worst-case *O*(*nq*) time (where *n* is
    /// `self.capacity()` and *q* is the length of the probe sequences
    /// in `other`)
    pub fn is_submap<V1, S1>(&self, other: &WeakValueHashMap<K, V1, S1>) -> bool
    where
        V1: WeakElement,
        V::Strong: PartialEq<V1::Strong>,
        S1: BuildHasher,
    {
        self.is_submap_with(other, |v, v1| v == v1)
    }

    /// Are the keys of `self` a subset of the keys of `other`?
    ///
    /// expected *O*(*n*) time; worst-case *O*(*nq*) time (where *n* is
    /// `self.capacity()` and *q* is the length of the probe sequences
    /// in `other`)
    pub fn domain_is_subset<V1, S1>(&self, other: &WeakValueHashMap<K, V1, S1>) -> bool
    where
        V1: WeakElement,
        S1: BuildHasher,
    {
        self.is_submap_with(other, |_, _| true)
    }
}

impl<K, V, V1, S, S1> PartialEq<WeakValueHashMap<K, V1, S1>> for WeakValueHashMap<K, V, S>
where
    K: Eq + Hash,
    V: WeakElement,
    V1: WeakElement,
    V::Strong: PartialEq<V1::Strong>,
    S: BuildHasher,
    S1: BuildHasher,
{
    fn eq(&self, other: &WeakValueHashMap<K, V1, S1>) -> bool {
        self.is_submap(other) && other.domain_is_subset(self)
    }
}

impl<K: Eq + Hash, V: WeakElement, S: BuildHasher> Eq for WeakValueHashMap<K, V, S> where
    V::Strong: Eq
{
}

impl<K: Eq + Hash, V: WeakElement, S: BuildHasher + Default> Default for WeakValueHashMap<K, V, S> {
    fn default() -> Self {
        WeakValueHashMap::with_hasher(Default::default())
    }
}

impl<K, V, S> iter::FromIterator<(K, V::Strong)> for WeakValueHashMap<K, V, S>
where
    K: Eq + Hash,
    V: WeakElement,
    S: BuildHasher + Default,
{
    fn from_iter<T: IntoIterator<Item = (K, V::Strong)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let min_size = iter.size_hint().0;
        let mut result = WeakValueHashMap::with_capacity_and_hasher(min_size, Default::default());
        result.extend(iter);
        result
    }
}

impl<K: Eq + Hash, V: WeakElement, const N: usize> From<[(K, V::Strong); N]>
    for WeakValueHashMap<K, V, RandomState>
{
    /// Converts an array of key-value pairs into a map.
    ///
    /// If any entries in the array have equal keys,
    /// all but one of the corresponding values will be dropped.
    fn from(value: [(K, V::Strong); N]) -> Self {
        Self::from_iter(value)
    }
}

impl<K, V, S> Extend<(K, V::Strong)> for WeakValueHashMap<K, V, S>
where
    K: Eq + Hash,
    V: WeakElement,
    S: BuildHasher,
{
    fn extend<T: IntoIterator<Item = (K, V::Strong)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        let min_size = iter.size_hint().0;
        self.reserve(min_size);

        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

impl<'a, K, V, S> Extend<(&'a K, &'a V::Strong)> for WeakValueHashMap<K, V, S>
where
    K: 'a + Eq + Hash + Clone,
    V: 'a + WeakElement,
    V::Strong: Clone,
    S: BuildHasher,
{
    fn extend<T: IntoIterator<Item = (&'a K, &'a V::Strong)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        let min_size = iter.size_hint().0;
        self.reserve(min_size);

        for (key, value) in iter {
            self.insert(key.clone(), value.clone());
        }
    }
}

impl<'a, K, V: WeakElement> Entry<'a, K, V> {
    /// Ensures a value is in the entry by inserting a default value
    /// if empty.
    ///
    /// *O*(1) time
    pub fn or_insert(self, default: V::Strong) -> V::Strong {
        self.or_insert_with(|| default)
    }

    /// Ensures a value is in the entry by inserting the result of the
    /// `default` function if empty, and returns a strong reference to
    /// the value in the entry.
    ///
    /// *O*(1) time
    pub fn or_insert_with<F: FnOnce() -> V::Strong>(self, default: F) -> V::Strong {
        match self {
            Entry::Occupied(occupied) => occupied.get_strong(),
            Entry::Vacant(vacant) => vacant.insert(default()),
        }
    }

    /// Ensures that a value is in the entry by inserting the result of calling the
    /// `default` function on this entry's key if the function is empty, and
    /// returns a strong reference to the value in the entry.
    pub fn or_insert_with_key<F>(self, default: F) -> V::Strong
    where
        F: FnOnce(&K) -> V::Strong,
    {
        match self {
            Entry::Occupied(occupied) => occupied.get_strong(),
            Entry::Vacant(vacant) => {
                let value = default(vacant.key());
                vacant.insert(value)
            }
        }
    }

    /// Returns a reference to this entry's key.
    ///
    /// *O*(1) time
    pub fn key(&self) -> &K {
        match *self {
            Entry::Occupied(ref occupied) => occupied.key(),
            Entry::Vacant(ref vacant) => vacant.key(),
        }
    }

    /// Inserts a value into this entry, and returns an [`OccupiedEntry`].
    ///
    /// *O*(1) time
    pub fn insert_entry(self, value: V::Strong) -> OccupiedEntry<'a, K, V> {
        match self {
            Entry::Occupied(mut occupied) => {
                occupied.insert(value);
                occupied
            }
            Entry::Vacant(vacant) => vacant.insert_entry(value),
        }
    }
}

impl<'a, K, V: WeakElement> OccupiedEntry<'a, K, V> {
    /// Gets a reference to the key held by the entry.
    ///
    /// *O*(1) time
    pub fn key(&self) -> &K {
        self.0.get().0
    }

    /// Takes ownership of the key and value, removing them from the map.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn remove_entry(self) -> (K, V::Strong) {
        self.0.remove()
    }

    /// Gets a reference to the value in the entry.
    ///
    /// *O*(1) time
    pub fn get(&self) -> &V::Strong {
        self.0.get().1
    }

    /// Gets a copy of the strong value reference stored in the entry.
    ///
    /// *O*(1) time
    pub fn get_strong(&self) -> V::Strong {
        V::clone(self.get())
    }

    /// Replaces the value in the entry with the given value, returning the old value.
    ///
    /// *O*(1) time
    pub fn insert(&mut self, value: V::Strong) -> V::Strong {
        self.0.insert(value)
    }

    /// Removes the entry, returning the value.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn remove(self) -> V::Strong {
        self.remove_entry().1
    }
}

impl<'a, K, V: WeakElement> VacantEntry<'a, K, V> {
    /// Gets a reference to the key that would be used when inserting a
    /// value through the `VacantEntry`.
    ///
    /// *O*(1) time
    pub fn key(&self) -> &K {
        self.0.key()
    }

    /// Returns an owned reference to the key.
    ///
    /// *O*(1) time
    pub fn into_key(self) -> K {
        self.0.into_key()
    }

    /// Inserts the value into the map, returning the same value.
    ///
    /// *O*(1) time
    pub fn insert(self, value: V::Strong) -> V::Strong {
        let occ = self.0.insert(value);
        V::clone(occ.get().1)
    }

    /// Inserts the key and value into the map, returning an `OccupiedEntry`.
    ///
    /// *O*(1) time
    pub fn insert_entry(self, value: V::Strong) -> OccupiedEntry<'a, K, V> {
        OccupiedEntry(self.0.insert(value))
    }
}

impl<K: Debug, V: WeakElement, S> Debug for WeakValueHashMap<K, V, S>
where
    V::Strong: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<'a, K: Debug, V: WeakElement> Debug for Entry<'a, K, V>
where
    V::Strong: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            Entry::Occupied(ref e) => e.fmt(f),
            Entry::Vacant(ref e) => e.fmt(f),
        }
    }
}

impl<'a, K: Debug, V: WeakElement> Debug for OccupiedEntry<'a, K, V>
where
    V::Strong: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a, K: Debug, V: WeakElement> Debug for VacantEntry<'a, K, V>
where
    V::Strong: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<K, V: WeakElement, S> IntoIterator for WeakValueHashMap<K, V, S> {
    type Item = (K, V::Strong);
    type IntoIter = IntoIter<K, V>;

    /// Creates an owning iterator from `self`.
    ///
    /// *O*(1) time (and *O*(*n*) time to dispose of the result)
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

impl<'a, K, V: WeakElement, S> IntoIterator for &'a WeakValueHashMap<K, V, S> {
    type Item = (&'a K, V::Strong);
    type IntoIter = Iter<'a, K, V>;

    /// Creates a borrowing iterator from `self`.
    ///
    /// *O*(1) time
    fn into_iter(self) -> Self::IntoIter {
        Iter(self.0.iter())
    }
}

impl<K, V: WeakElement, S> WeakValueHashMap<K, V, S> {
    /// Gets an iterator over the keys and values.
    ///
    /// *O*(1) time
    pub fn iter(&self) -> Iter<'_, K, V> {
        self.into_iter()
    }

    /// Gets an iterator over the keys.
    ///
    /// *O*(1) time
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys(self.iter())
    }

    /// Gets an iterator over the values.
    ///
    /// *O*(1) time
    pub fn values(&self) -> Values<'_, K, V> {
        Values(self.iter())
    }

    /// Gets a draining iterator, which removes all the values but retains the storage.
    ///
    /// *O*(1) time (and *O*(*n*) time to dispose of the result)
    pub fn drain(&mut self) -> Drain<'_, K, V> {
        Drain(self.0.drain())
    }

    into_kv_methods! {}

    /// Gets an iterator that removes and returns elements matching a given predicate.
    ///
    /// Expired elements are also removed.
    ///
    /// If this iterator is dropped before it is completed, then no further
    /// elements are removed.
    /// (This is in contrast to the behavior of [`drain`](Self::drain)).
    ///
    /// *O*(1) time
    pub fn extract_if<'a, F>(&'a mut self, mut f: F) -> ExtractIf<'a, K, V, F>
    where
        F: FnMut(&K, V::Strong) -> bool + 'a,
    {
        ExtractIf {
            inner: self.0.extract_if(move |e| {
                if let Some(v) = e.1.val.view() {
                    f(&e.0.val, v)
                } else {
                    true
                }
            }),
            _phantom: PhantomData,
        }
    }
}

/// An iterator that removes members that match a given predicate.
pub struct ExtractIf<'a, K, V: WeakElement, F> {
    /// The underlying iterator.
    inner: inner::ExtractIf<'a, inner::Owned<K>, inner::WeakV<V>>,
    /// A marker so that F does not appear unused.
    _phantom: PhantomData<F>,
}

impl<'a, K, V: WeakElement, F> Iterator for ExtractIf<'a, K, V, F> {
    type Item = (K, V::Strong);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

#[cfg(test)]
mod test {
    use super::WeakValueHashMap;
    use crate::compat::rc::Weak;

    crate::tests::common::empty_constructor_tests! {WeakValueHashMap<u32, Weak<u32>>}
}
