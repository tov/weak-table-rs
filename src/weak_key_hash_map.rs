//! A hash map where the keys are held by weak pointers and compared by key value.

use super::inner;
use super::traits::*;
use super::*;
use crate::common::*;

pub use super::WeakKeyHashMap;

/// Represents an entry in the table which may be occupied or vacant.
#[allow(clippy::exhaustive_enums)]
pub enum Entry<'a, K: 'a + WeakKey, V: 'a> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, K, V>),
    /// A vacant entry.
    Vacant(VacantEntry<'a, K, V>),
}

/// An occupied entry, which can be removed, modified, or viewed.
pub struct OccupiedEntry<'a, K: 'a + WeakKey, V: 'a>(
    inner::OccupiedEntry<'a, inner::WeakK<K>, inner::Owned<V>>,
);

/// A vacant entry, which can be inserted in or viewed.
pub struct VacantEntry<'a, K: 'a + WeakKey, V: 'a>(
    inner::VacantEntry<'a, inner::WeakK<K>, inner::Owned<V>>,
);

/// An iterator over the keys and values of the weak hash map.
#[derive(Clone, Debug)]
pub struct Iter<'a, K: 'a, V: 'a>(inner::Iter<'a, inner::WeakK<K>, inner::Owned<V>>);

impl<'a, K: WeakElement, V> Iterator for Iter<'a, K, V> {
    type Item = (K::Strong, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

#[derive(Debug)]
/// An iterator over the keys and mutable values of the weak hash map.
pub struct IterMut<'a, K: 'a, V: 'a>(inner::IterMut<'a, inner::WeakK<K>, inner::Owned<V>>);

impl<'a, K: WeakElement, V> Iterator for IterMut<'a, K, V> {
    type Item = (K::Strong, &'a mut V);

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

impl<'a, K: WeakElement, V> Iterator for Keys<'a, K, V> {
    type Item = K::Strong;

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

impl<'a, K: WeakElement, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

#[derive(Debug)]
/// An iterator over the mutable values of the weak hash map.
pub struct ValuesMut<'a, K: 'a, V: 'a>(IterMut<'a, K, V>);

impl<'a, K: WeakElement, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

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
pub struct Drain<'a, K: 'a, V: 'a>(inner::Drain<'a, inner::WeakK<K>, inner::Owned<V>>);

impl<'a, K: WeakElement, V> Iterator for Drain<'a, K, V> {
    type Item = (K::Strong, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

/// An iterator that consumes a weak hash map, leaving it empty.
pub struct IntoIter<K, V>(inner::IntoIter<inner::WeakK<K>, inner::Owned<V>>);

impl<K: WeakElement, V> Iterator for IntoIter<K, V> {
    type Item = (K::Strong, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

into_kv_types!(K::Strong, V where {K: WeakElement});

universal_hashless_members! {
    WeakKeyHashMap ("`WeakKeyHashMap`", a "map") inner::Table::new {K,V}
}

impl<K: WeakKey, V, S: BuildHasher> WeakKeyHashMap<K, V, S> {
    universal_key_independent_members! {"mappings"}

    /// Gets the requested entry.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn entry(&mut self, key: K::Strong) -> Entry<'_, K, V> {
        match self.0.entry(key) {
            inner::Entry::Occupied(occ) => Entry::Occupied(OccupiedEntry(occ)),
            inner::Entry::Vacant(vac) => Entry::Vacant(VacantEntry(vac)),
        }
    }
    /// Returns a reference to the value corresponding to the key.
    ///
    /// Returns `None` if no matching key is found.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        Q: ?Sized + Hash + Eq,
        K::Key: Borrow<Q>,
    {
        Some(self.0.find(key)?.1)
    }

    /// Returns true if the map contains the specified key.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        Q: ?Sized + Hash + Eq,
        K::Key: Borrow<Q>,
    {
        self.0.find(key).is_some()
    }

    /// Returns a strong reference to the key, if found.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn get_key<Q>(&self, key: &Q) -> Option<K::Strong>
    where
        Q: ?Sized + Hash + Eq,
        K::Key: Borrow<Q>,
    {
        Some(self.0.find(key)?.0)
    }

    /// Returns a pair of a strong reference to the key, and a reference to the value, if present.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn get_both<Q>(&self, key: &Q) -> Option<(K::Strong, &V)>
    where
        Q: ?Sized + Hash + Eq,
        K::Key: Borrow<Q>,
    {
        self.0.find(key)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// Returns `None` if no matching key is found.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        Q: ?Sized + Hash + Eq,
        K::Key: Borrow<Q>,
    {
        Some(self.0.find_mut(key)?.1)
    }

    /// Returns a pair of a strong reference to the key, and a mutable reference to the value,
    /// if present.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn get_both_mut<Q>(&mut self, key: &Q) -> Option<(K::Strong, &mut V)>
    where
        Q: ?Sized + Hash + Eq,
        K::Key: Borrow<Q>,
    {
        self.0.find_mut(key)
    }

    /// Looks up mutable references to the values corresponding to several keys
    /// at a time.
    ///
    /// (Because of borrowing rules, Rust doesn't allow you to call `get_mut()` again
    /// while the result of a previous `get_mut()` is still live.  This method exists
    /// to work around that limitation.)
    ///
    /// Only one mutable reference can exist to any given value at a time.
    /// Therefore, all keys must refer to different values, or this
    /// method will panic.
    ///
    /// expected *O*(1 `N^2`) time; worst-case *O*(*p* `N^2`) time,
    /// where N is the length of the array.
    ///
    /// # Panics
    ///
    /// Panics if any keys refer to the same value.
    pub fn get_disjoint_mut<Q, const N: usize>(&mut self, ks: [&Q; N]) -> [Option<&mut V>; N]
    where
        Q: Hash + Eq + ?Sized,
        K::Key: Borrow<Q>,
    {
        self.0.get_disjoint_mut(ks).map(|e| e.map(|(_k, v)| v))
    }

    /// Looks up mutable references to the values corresponding to several keys
    /// at a time.  Returns those references along with their keys as stored in
    /// the table.
    ///
    /// (Because of borrowing rules, Rust doesn't allow you to call `get_mut()` again
    /// while the result of a previous `get_mut()` is still live.  This method exists
    /// to work around that limitation.)
    ///
    /// Only one mutable reference can exist to any given value at a time.
    /// Therefore, all keys must refer to different values, or this
    /// method will panic.
    ///
    /// expected *O*(1 `N^2`) time; worst-case *O*(*p* `N^2`) time,
    /// where N is the length of the array.
    ///
    /// # Panics
    ///
    /// Panics if any keys refer to the same value.
    pub fn get_both_disjoint_mut<Q, const N: usize>(
        &mut self,
        ks: [&Q; N],
    ) -> [Option<(K::Strong, &mut V)>; N]
    where
        Q: Hash + Eq + ?Sized,
        K::Key: Borrow<Q>,
    {
        self.0.get_disjoint_mut(ks)
    }

    /// Unconditionally inserts the value, returning the old value if already present.
    ///
    /// Unlike `std::collections::HashMap`, this replaces the key even the entry was occupied.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn insert(&mut self, key: K::Strong, value: V) -> Option<V> {
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
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        Q: ?Sized + Hash + Eq,
        K::Key: Borrow<Q>,
    {
        Some(self.0.find_entry(key)?.remove().1)
    }

    /// Removes the entry with the given key, if it exists, and returns both the
    /// key and value.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn remove_entry<Q>(&mut self, key: &Q) -> Option<(K::Strong, V)>
    where
        Q: ?Sized + Hash + Eq,
        K::Key: Borrow<Q>,
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
        F: FnMut(K::Strong, &mut V) -> bool,
    {
        // TODO: It would be better to use a retain method on Table, but I've
        // run into lifetime issues there. See "TODO retain" in inner/table.rs
        self.0.table.retain(|(k, v)| {
            if let Some(k) = k.val.view() {
                f(k, &mut v.val)
            } else {
                false
            }
        });
    }

    /// Is this map a submap of the other under the given value comparison `cmp`?
    ///
    /// In particular, for every key `k` of `self`,
    ///
    ///  - `k` must also be a key of `other` and
    ///  - `cmp(self[k], other[k])` must hold.
    ///
    /// expected *O*(*n*) time; worst-case *O*(*nq*) time (where *n* is
    /// `self.capacity()` and *q* is the length of the probe sequences
    /// in `other`)
    pub fn is_submap_with<F, S1, V1>(&self, other: &WeakKeyHashMap<K, V1, S1>, mut cmp: F) -> bool
    where
        F: FnMut(&V, &V1) -> bool,
        S1: BuildHasher,
    {
        for (key, value1) in self {
            if let Some(value2) = K::with_key(&key, |k| other.get(k)) {
                if !cmp(value1, value2) {
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
    pub fn is_submap<V1, S1>(&self, other: &WeakKeyHashMap<K, V1, S1>) -> bool
    where
        V: PartialEq<V1>,
        S1: BuildHasher,
    {
        self.is_submap_with(other, PartialEq::eq)
    }

    /// Are the keys of `self` a subset of the keys of `other`?
    ///
    /// expected *O*(*n*) time; worst-case *O*(*nq*) time (where *n* is
    /// `self.capacity()` and *q* is the length of the probe sequences
    /// in `other`)
    pub fn domain_is_subset<V1, S1>(&self, other: &WeakKeyHashMap<K, V1, S1>) -> bool
    where
        S1: BuildHasher,
    {
        self.is_submap_with(other, |_, _| true)
    }
}

impl<K, V, V1, S, S1> PartialEq<WeakKeyHashMap<K, V1, S1>> for WeakKeyHashMap<K, V, S>
where
    K: WeakKey,
    V: PartialEq<V1>,
    S: BuildHasher,
    S1: BuildHasher,
{
    fn eq(&self, other: &WeakKeyHashMap<K, V1, S1>) -> bool {
        self.is_submap(other) && other.domain_is_subset(self)
    }
}

impl<K: WeakKey, V: Eq, S: BuildHasher> Eq for WeakKeyHashMap<K, V, S> {}

impl<'a, K, V, S, Q> ops::Index<&'a Q> for WeakKeyHashMap<K, V, S>
where
    K: WeakKey,
    K::Key: Borrow<Q>,
    S: BuildHasher,
    Q: ?Sized + Eq + Hash,
{
    type Output = V;

    fn index(&self, index: &'a Q) -> &Self::Output {
        self.get(index).expect("Index::index: key not found")
    }
}

impl<'a, K, V, S, Q> ops::IndexMut<&'a Q> for WeakKeyHashMap<K, V, S>
where
    K: WeakKey,
    K::Key: Borrow<Q>,
    S: BuildHasher,
    Q: ?Sized + Eq + Hash,
{
    fn index_mut(&mut self, index: &'a Q) -> &mut Self::Output {
        self.get_mut(index)
            .expect("IndexMut::index_mut: key not found")
    }
}

impl<K, V, S> iter::FromIterator<(K::Strong, V)> for WeakKeyHashMap<K, V, S>
where
    K: WeakKey,
    S: BuildHasher + Default,
{
    fn from_iter<T: IntoIterator<Item = (K::Strong, V)>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let min_size = iter.size_hint().0;
        let mut result = WeakKeyHashMap::with_capacity_and_hasher(min_size, Default::default());
        result.extend(iter);
        result
    }
}

impl<K: WeakKey, V, const N: usize> From<[(K::Strong, V); N]>
    for WeakKeyHashMap<K, V, RandomState>
{
    /// Converts an array of key-value pairs into a map.
    ///
    /// If any entries in the array have equal keys,
    /// all but one of the corresponding values will be dropped.
    fn from(value: [(K::Strong, V); N]) -> Self {
        Self::from_iter(value)
    }
}

impl<K, V, S> iter::Extend<(K::Strong, V)> for WeakKeyHashMap<K, V, S>
where
    K: WeakKey,
    S: BuildHasher,
{
    fn extend<T: IntoIterator<Item = (K::Strong, V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        let min_size = iter.size_hint().0;
        self.reserve(min_size);
        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

impl<'a, K, V, S> iter::Extend<(&'a K::Strong, &'a V)> for WeakKeyHashMap<K, V, S>
where
    K: 'a + WeakKey,
    K::Strong: Clone,
    V: 'a + Clone,
    S: BuildHasher,
{
    fn extend<T: IntoIterator<Item = (&'a K::Strong, &'a V)>>(&mut self, iter: T) {
        let iter = iter.into_iter();
        let min_size = iter.size_hint().0;
        self.reserve(min_size);
        for (key, value) in iter {
            self.insert(key.clone(), value.clone());
        }
    }
}

impl<'a, K: WeakKey, V> Entry<'a, K, V> {
    /// Ensures a value is in the entry by inserting a default value
    /// if empty, and returns a mutable reference to the value in the
    /// entry.
    ///
    /// *O*(1) time
    pub fn or_insert(self, default: V) -> &'a mut V {
        self.or_insert_with(|| default)
    }

    /// Ensures a value is in the entry by inserting the result of the
    /// `default` function if empty, and returns a mutable reference to
    /// the value in the entry.
    ///
    /// *O*(1) time
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(occupied) => occupied.into_mut(),
            Entry::Vacant(vacant) => vacant.insert(default()),
        }
    }

    /// Ensures that a value is in the entry by inserting the result of calling the
    /// `default` function on this entry's key if the function is empty, and
    /// returns a mutable reference to the value in the entry.
    pub fn or_insert_with_key<F>(self, default: F) -> &'a mut V
    where
        F: FnOnce(&K::Strong) -> V,
    {
        match self {
            Entry::Occupied(occupied) => occupied.into_mut(),
            Entry::Vacant(vacant) => {
                let value = default(vacant.key());
                vacant.insert(value)
            }
        }
    }

    /// Returns a reference to this entry's key.
    ///
    /// *O*(1) time
    pub fn key(&self) -> &K::Strong {
        match *self {
            Entry::Occupied(ref occupied) => occupied.key(),
            Entry::Vacant(ref vacant) => vacant.key(),
        }
    }

    /// Inserts a value into this entry, and returns an [`OccupiedEntry`].
    ///
    /// *O*(1) time
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
        match self {
            Entry::Occupied(mut occupied) => {
                occupied.insert(value);
                occupied
            }
            Entry::Vacant(vacant) => vacant.insert_entry(value),
        }
    }

    /// If this entry is occupied, uses `f` to modify its value in place.
    ///
    /// (Otherwise, if the entry is vacant, does nothing.)
    ///
    /// *O*(1) time
    pub fn and_modify<F>(mut self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        if let Entry::Occupied(occupied) = &mut self {
            f(occupied.get_mut());
        }
        self
    }
}

impl<'a, K: WeakKey, V> OccupiedEntry<'a, K, V> {
    /// Gets a reference to the key held by the entry.
    ///
    /// *O*(1) time
    pub fn key(&self) -> &K::Strong {
        self.0.get().0
    }

    /// Takes ownership of the key and value, removing them from the map.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn remove_entry(self) -> (K::Strong, V) {
        self.0.remove()
    }

    /// Gets a reference to the value in the entry.
    ///
    /// *O*(1) time
    pub fn get(&self) -> &V {
        self.0.get().1
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// *O*(1) time
    pub fn get_mut(&mut self) -> &mut V {
        // TODO: It would be better to use a get_mut method on inner::OccupiedEntry, but I've
        // run into lifetime issues there. See "TODO get_mut" in inner/table.rs
        &mut self.0.inner.get_mut().1.val
    }

    /// Turns the entry into a mutable reference to the value borrowed from the map.
    ///
    /// *O*(1) time
    pub fn into_mut(self) -> &'a mut V {
        self.0.into_mut()
    }

    /// Replaces the value in the entry with the given value.
    ///
    /// Returns the previous value.
    ///
    /// *O*(1) time
    pub fn insert(&mut self, mut value: V) -> V {
        mem::swap(&mut value, self.get_mut());
        value
    }

    /// Removes the entry, returning the value.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn remove(self) -> V {
        self.remove_entry().1
    }
}

impl<'a, K: WeakKey, V> VacantEntry<'a, K, V> {
    /// Gets a reference to the key that would be used when inserting a
    /// value through the `VacantEntry`.
    ///
    /// *O*(1) time
    pub fn key(&self) -> &K::Strong {
        self.0.key()
    }

    /// Returns an owned reference to the key.
    ///
    /// *O*(1) time
    pub fn into_key(self) -> K::Strong {
        self.0.into_key()
    }

    /// Inserts the key and value into the map and return a mutable
    /// reference to the value.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn insert(self, value: V) -> &'a mut V {
        let occupied = self.0.insert(value);
        occupied.into_mut()
    }

    /// Inserts the key and value into the map, returning an `OccupiedEntry`.
    ///
    /// *O*(1) time
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
        OccupiedEntry(self.0.insert(value))
    }
}

impl<K: WeakElement, V: Debug, S> Debug for WeakKeyHashMap<K, V, S>
where
    K::Strong: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

debug_for_entry! {where {
    K: WeakKey,
    K::Strong: Debug,
    V: Debug}
}

impl<K: WeakElement, V, S> IntoIterator for WeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, V);
    type IntoIter = IntoIter<K, V>;

    /// Creates an owning iterator from `self`.
    ///
    /// *O*(1) time (and *O*(*n*) time to dispose of the result)
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

impl<'a, K: WeakElement, V, S> IntoIterator for &'a WeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, &'a V);
    type IntoIter = Iter<'a, K, V>;

    /// Creates a borrowing iterator from `self`.
    ///
    /// *O*(1) time
    fn into_iter(self) -> Self::IntoIter {
        Iter(self.0.iter())
    }
}

impl<'a, K: WeakElement, V, S> IntoIterator for &'a mut WeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    /// Creates a borrowing iterator from `self`.
    ///
    /// *O*(1) time
    fn into_iter(self) -> Self::IntoIter {
        IterMut(self.0.iter_mut())
    }
}

impl<K: WeakElement, V, S> WeakKeyHashMap<K, V, S> {
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

    /// Gets an iterator over the keys and mutable values.
    ///
    /// *O*(1) time
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        self.into_iter()
    }

    /// Gets an iterator over the mutable values.
    ///
    /// *O*(1) time
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut(self.iter_mut())
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
        F: FnMut(K::Strong, &mut V) -> bool + 'a,
    {
        ExtractIf {
            inner: self.0.extract_if(move |e| {
                if let Some(k) = e.0.val.view() {
                    f(k, &mut e.1.val)
                } else {
                    true
                }
            }),
            _phantom: PhantomData,
        }
    }
}

/// An iterator that removes members that match a given predicate.
pub struct ExtractIf<'a, K: WeakElement, V, F> {
    /// The underlying iterator.
    inner: inner::ExtractIf<'a, inner::WeakK<K>, inner::Owned<V>>,
    /// A marker so that F does not appear unused.
    _phantom: PhantomData<F>,
}

impl<'a, K: WeakElement, V, F> Iterator for ExtractIf<'a, K, V, F> {
    type Item = (K::Strong, V);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

#[cfg(test)]
mod test {
    #![allow(clippy::print_stderr)]

    use super::{Entry, WeakKeyHashMap};
    use crate::{
        compat::{
            eprintln, format,
            rc::{Rc, Weak},
            RandomState, String, ToString as _, Vec,
        },
        tests::util::VecDebugAsMap,
        util,
    };

    crate::tests::common::empty_constructor_tests! {WeakKeyHashMap<Weak<u8>, u32>}

    #[test]
    fn simple() {
        let mut map: WeakKeyHashMap<Weak<str>, usize> = WeakKeyHashMap::new();
        assert_eq!(map.len(), 0);
        assert!(!map.contains_key("five"));

        let five: Rc<str> = Rc::from(String::from("five"));
        map.insert(five.clone(), 5);

        assert_eq!(map.len(), 1);
        assert!(map.contains_key("five"));

        drop(five);

        assert_eq!(map.len(), 1);
        assert!(!map.contains_key("five"));

        map.remove_expired();

        assert_eq!(map.len(), 0);
        assert!(!map.contains_key("five"));
    }

    #[test]
    fn simple_arc() {
        use crate::compat::sync::{Arc, Weak};
        let mut map: WeakKeyHashMap<Weak<str>, usize> = WeakKeyHashMap::new();
        assert_eq!(map.len(), 0);
        assert!(!map.contains_key("five"));

        let five: Arc<str> = Arc::from(String::from("five"));
        map.insert(five.clone(), 5);

        assert_eq!(map.len(), 1);
        assert!(map.contains_key("five"));

        drop(five);

        assert_eq!(map.len(), 1);
        assert!(!map.contains_key("five"));

        map.remove_expired();

        assert_eq!(map.len(), 0);
        assert!(!map.contains_key("five"));
    }

    #[test]
    fn access_hasher() {
        let bh = RandomState::new();

        let map: WeakKeyHashMap<Weak<str>, usize> = WeakKeyHashMap::with_hasher(bh.clone());

        assert_eq!(
            util::hash_one(&bh, "hello world"),
            util::hash_one(map.hasher(), "hello world")
        );
    }

    #[test]
    fn load_factor() {
        let mut rcs: Vec<Rc<u32>> = (0..50).map(Rc::new).collect();
        let weakmap: WeakKeyHashMap<Weak<u32>, u32> =
            rcs.iter().map(|n| (n.clone(), *n.as_ref())).collect();
        rcs.retain(|n| **n % 3 != 0);

        let load = weakmap.load_factor();
        assert!(load < 1.0);
        assert!(load > 0.0);
    }

    #[test]
    fn is_submap() {
        let mut rcs: Vec<Rc<u32>> = (0..50).map(Rc::new).collect();
        let weakmap: WeakKeyHashMap<Weak<u32>, u32> = rcs
            .iter()
            .take(25)
            .map(|n| (n.clone(), *n.as_ref()))
            .collect();
        let mut weakmap2 = weakmap.clone();

        assert!(weakmap.is_submap(&weakmap2));
        assert!(weakmap2.is_submap(&weakmap));

        weakmap2.extend(rcs.iter().skip(25).map(|n| (n, n.as_ref())));
        assert!(weakmap.is_submap(&weakmap2));
        assert!(!weakmap2.is_submap(&weakmap));

        weakmap2[&0] = 12;
        assert!(!weakmap.is_submap(&weakmap2));
        assert!(!weakmap2.is_submap(&weakmap));

        let _ = rcs.remove(0);
        assert!(weakmap.is_submap(&weakmap2));
    }

    #[test]
    fn entry_methods() {
        let rcs: Vec<Rc<u32>> = (0..5).map(Rc::new).collect();
        let mut weakmap: WeakKeyHashMap<Weak<u32>, u32> =
            rcs.iter().map(|n| (n.clone(), *n.as_ref())).collect();

        let seven = Rc::new(7);
        let ptr = weakmap.entry(seven.clone()).or_insert(14);
        assert_eq!(*ptr, 14);
        *ptr = 21;

        assert_eq!(weakmap.get(&7), Some(&21));

        let twelve = Rc::new(12);
        let e = weakmap.entry(twelve.clone());
        if let Entry::Vacant(v) = e {
            let t2 = v.into_key();
            assert_eq!(*t2, 12);
        } else {
            panic!();
        }
        assert!(!weakmap.contains_key(&12));
    }

    #[test]
    fn or_insert_with() {
        let rcs: Vec<Rc<u32>> = (0..5).map(Rc::new).collect();
        let mut weakmap: WeakKeyHashMap<Weak<u32>, u32> =
            rcs.iter().map(|n| (n.clone(), **n)).collect();
        let seven = Rc::new(7);
        let eight = Rc::new(8);

        // Absent key case:
        let ptr: &mut u32 = weakmap.entry(seven.clone()).or_insert_with(|| 14);
        assert_eq!(*ptr, 14);
        let ptr: &mut u32 = weakmap.entry(eight.clone()).or_insert_with_key(|k| **k * 2);
        assert_eq!(*ptr, 16);

        // Present key case:
        let one = Rc::new(1);
        let ptr: &mut u32 = weakmap.entry(one.clone()).or_insert_with(|| 14);
        assert_eq!(*ptr, 1);
        let ptr: &mut u32 = weakmap.entry(one.clone()).or_insert_with_key(|k| **k * 2);
        assert_eq!(*ptr, 1);
    }

    #[test]
    fn entry_insert_entry() {
        let rcs: Vec<Rc<u32>> = (0..5).map(Rc::new).collect();
        let mut weakmap: WeakKeyHashMap<Weak<u32>, u32> =
            rcs.iter().map(|n| (n.clone(), **n)).collect();

        let one = Rc::new(1);
        let ten = Rc::new(10);

        let e1: super::OccupiedEntry<'_, Weak<u32>, u32> =
            weakmap.entry(one.clone()).insert_entry(1001);
        assert_eq!(e1.key(), &one);
        assert_eq!(e1.get(), &1001);

        let e2: super::OccupiedEntry<'_, Weak<u32>, u32> =
            weakmap.entry(ten.clone()).insert_entry(1010);
        assert_eq!(e2.key(), &ten);
        assert_eq!(e2.get(), &1010);

        assert_eq!(weakmap.get(&1), Some(&1001));
        assert_eq!(weakmap.get(&10), Some(&1010));
    }

    #[test]
    fn entry_and_modify() {
        let rcs: Vec<Rc<u32>> = (0..5).map(Rc::new).collect();
        let mut weakmap: WeakKeyHashMap<Weak<u32>, u32> =
            rcs.iter().map(|n| (n.clone(), **n)).collect();

        let one = Rc::new(1);
        let ten = Rc::new(10);

        let e = weakmap.entry(one.clone()).and_modify(|v| *v *= 2);
        assert!(matches!(e, Entry::Occupied(e) if e.get() == &2));

        let e = weakmap.entry(ten.clone()).and_modify(|v| *v *= 2);
        assert!(matches!(e, Entry::Vacant(_)));
    }

    #[test]
    fn vacant_insert_entry() {
        let mut weakmap: WeakKeyHashMap<Weak<u32>, u32> = Default::default();
        let five = Rc::new(5);

        let Entry::Vacant(e) = weakmap.entry(five.clone()) else {
            panic!("Not vacant");
        };
        let e: super::OccupiedEntry<'_, Weak<u32>, u32> = e.insert_entry(500);
        assert_eq!(e.get(), &500);
    }

    #[test]
    fn from_array() {
        let a = [(Rc::new(5), 25), (Rc::new(7), 49), (Rc::new(9), 81)];
        let v = a.to_vec();

        let map: WeakKeyHashMap<Weak<u32>, u32> = WeakKeyHashMap::from(a);
        assert_eq!(map.iter().count(), 3);
        let mut v2: Vec<_> = map.iter().map(|(k, v)| (k, *v)).collect();
        v2.sort();
        assert_eq!(v, v2);
    }

    // From https://github.com/tov/weak-table-rs/issues/1#issuecomment-461858060
    #[test]
    fn insert_and_check() {
        let mut rcs: Vec<Rc<u32>> = Vec::new();

        for i in 0..50 {
            rcs.push(Rc::new(i));
        }

        let mut weakmap: WeakKeyHashMap<Weak<u32>, f32> = WeakKeyHashMap::new();

        for key in rcs.iter().cloned() {
            let f = *key as f32 + 0.1;
            weakmap.insert(key, f);
        }

        let mut count = 0;

        for key in &rcs {
            assert_eq!(weakmap.get(key), Some(&(**key as f32 + 0.1)));

            match weakmap.entry(Rc::clone(key)) {
                Entry::Occupied(_) => count += 1,
                Entry::Vacant(_) => eprintln!("WeakKeyHashMap: missing: {}", *key),
            }
        }

        assert_eq!(count, rcs.len());
    }

    #[test]
    fn extract_if() {
        let rcs: Vec<Rc<u32>> = (0..50).map(Rc::new).collect();
        let mut weakmap: WeakKeyHashMap<Weak<u32>, u32> =
            rcs.iter().map(|k| (k.clone(), *k.as_ref())).collect();
        let even_numbers: crate::compat::HashSet<u32> = (0..50).filter(|n| n % 2 == 0).collect();

        let evens: Vec<_> = weakmap
            .extract_if(|k, v| {
                debug_assert!(k.as_ref() == v);
                *v *= 2;
                even_numbers.contains(k.as_ref())
            })
            .collect();

        assert_eq!(weakmap.iter().count(), 25);
        assert_eq!(evens.len(), 25);
    }

    #[test]
    fn failed_try_reserve() {
        let rcs: Vec<Rc<u32>> = (0..1000).map(Rc::new).collect();
        let mut map: WeakKeyHashMap<Weak<u32>, u32> =
            rcs.iter().map(|n| (n.clone(), **n)).collect();

        // This one will cause an integer overflow in our code.
        let e = map.try_reserve(usize::MAX - 500);
        assert!(matches!(e, Err(crate::TryReserveError::CapacityOverflow)));
        assert_eq!(
            e.expect_err("Already checked").to_string(),
            "Allocation failed: arithmetic overflow in capacity calculation"
        );

        // This one will cause an integer overflow in hashbrown.
        let e = map.try_reserve(usize::MAX / 4);
        assert!(matches!(e, Err(crate::TryReserveError::CapacityOverflow)));
    }

    #[test]
    fn debug_map() {
        let rcs: Vec<Rc<u32>> = (0..20).map(Rc::new).collect();
        let map: WeakKeyHashMap<Weak<u32>, u32> =
            rcs.iter().map(|n| (n.clone(), **n * 7)).collect();
        let vec: VecDebugAsMap<_, _> = map.iter().collect();
        assert_eq!(format!("{map:?}"), format!("{vec:?}"));
    }

    #[test]
    fn debug_entry() {
        let three = Rc::new(3);
        let mut map = WeakKeyHashMap::<Weak<u32>, u32>::new();
        map.insert(three.clone(), 9);
        let e1 = map.entry(three.clone());
        assert_eq!(format!("{e1:?}"), "OccupiedEntry { key: 3, val: 9 }");

        let four = Rc::new(4);
        let e2 = map.entry(four.clone());
        assert_eq!(format!("{e2:?}"), "VacantEntry { key: 4 }");
    }
}
