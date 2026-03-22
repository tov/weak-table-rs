//! A hash map where the keys are held by weak pointers and compared by key value.

use super::inner;
use super::size_policy::*;
use super::traits::*;
use super::*;

pub use super::WeakKeyHashMap;

pub(super) type InnerTable<K, V, S> = inner::Table<inner::WeakK<K>, inner::Owned<V>, S>;
type InnerOccupiedEntry<'a, K, V> = inner::OccupiedEntry<'a, inner::WeakK<K>, inner::Owned<V>>;
type InnerVacantEntry<'a, K, V> = inner::VacantEntry<'a, inner::WeakK<K>, inner::Owned<V>>;

/// Represents an entry in the table which may be occupied or vacant.
pub enum Entry<'a, K: 'a + WeakKey, V: 'a> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

/// An occupied entry, which can be removed or viewed.
pub struct OccupiedEntry<'a, K: 'a + WeakKey, V: 'a>(InnerOccupiedEntry<'a, K, V>);

/// A vacant entry, which can be inserted in or viewed.
pub struct VacantEntry<'a, K: 'a + WeakKey, V: 'a>(InnerVacantEntry<'a, K, V>);

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

/// An iterator that consumes the values of a weak hash map, leaving it empty.
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

impl<K: WeakKey, V> WeakKeyHashMap<K, V, RandomState> {
    /// Creates an empty `WeakKeyHashMap`.
    ///
    /// *O*(1) time
    pub fn new() -> Self {
        Self::with_capacity(DEFAULT_INITIAL_CAPACITY)
    }

    /// Creates an empty `WeakKeyHashMap` with the given capacity.
    ///
    /// *O*(*n*) time
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, Default::default())
    }
}

impl<K: WeakKey, V, S: BuildHasher> WeakKeyHashMap<K, V, S> {
    /// Creates an empty `WeakKeyHashMap` with the given capacity and hasher.
    ///
    /// *O*(*n*) time
    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_capacity_and_hasher(DEFAULT_INITIAL_CAPACITY, hash_builder)
    }

    /// Creates an empty `WeakKeyHashMap` with the given capacity and hasher.
    ///
    /// *O*(*n*) time
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        WeakKeyHashMap(InnerTable::new(capacity, hash_builder))
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
    /// *O*(*n*) time
    pub fn reserve(&mut self, additional_capacity: usize) {
        self.0
            .try_reserve(additional_capacity)
            .expect("Unable to reserve additional capacity");
    }

    /// Shrinks the capacity to the minimum allowed to hold the current number of elements.
    ///
    /// *O*(*n*) time
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit();
    }

    /// Returns an over-approximation of the number of elements.
    ///
    /// *O*(1) time
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
        (self.len() as f32 + 1.0) / self.capacity() as f32
    }

    /// Gets the requested entry.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn entry(&mut self, key: K::Strong) -> Entry<'_, K, V> {
        match self.0.entry(key) {
            inner::Entry::Occupied(occ) => Entry::Occupied(OccupiedEntry(occ)),
            inner::Entry::Vacant(vac) => Entry::Vacant(VacantEntry(vac)),
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

    /// Unconditionally inserts the value, returning the old value if already present.
    ///
    /// Unlike `std::collections::HashMap`, this replaced the key even if occupied.
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

    /// Removes all mappings not satisfying the given predicate.
    ///
    /// Also removes any expired mappings.
    ///
    /// *O*(*n*) time
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(K::Strong, &mut V) -> bool,
    {
        //        XXXX
        self.0.table.retain(|(k, v)| {
            if let Some(k) = k.val.view() {
                f(k, &mut v.val)
            } else {
                false
            }
        })
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

impl<K: WeakKey, V, S: BuildHasher + Default> Default for WeakKeyHashMap<K, V, S> {
    fn default() -> Self {
        WeakKeyHashMap::with_hasher(Default::default())
    }
}

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
        // TODO: Use size_hint.
        let mut result = WeakKeyHashMap::with_hasher(Default::default());
        result.extend(iter);
        result
    }
}

impl<K, V, S> iter::Extend<(K::Strong, V)> for WeakKeyHashMap<K, V, S>
where
    K: WeakKey,
    S: BuildHasher,
{
    fn extend<T: IntoIterator<Item = (K::Strong, V)>>(&mut self, iter: T) {
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
    /// default function if empty, and returns a mutable reference to
    /// the value in the entry.
    ///
    /// *O*(1) time
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(occupied) => occupied.into_mut(),
            Entry::Vacant(vacant) => vacant.insert(default()),
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
}

impl<'a, K: WeakKey, V> OccupiedEntry<'a, K, V> {
    /// Gets a reference to the key held by the entry.
    ///
    /// *O*(1) time
    pub fn key(&self) -> &K::Strong {
        self.0.get().0
    }

    /// Takes ownership of the key and value from the map.
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
        // XXXX
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

    /// Returns ownership of the key.
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
}

impl<K: WeakElement, V: Debug, S> Debug for WeakKeyHashMap<K, V, S>
where
    K::Strong: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<'a, K: WeakKey, V: Debug> Debug for OccupiedEntry<'a, K, V>
where
    K::Strong: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a, K: WeakKey, V> Debug for VacantEntry<'a, K, V>
where
    K::Strong: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a, K: WeakKey, V: Debug> Debug for Entry<'a, K, V>
where
    K::Strong: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Entry::Occupied(occupied_entry) => occupied_entry.fmt(f),
            Entry::Vacant(vacant_entry) => vacant_entry.fmt(f),
        }
    }
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
}

#[cfg(test)]
mod test {
    use super::{Entry, WeakKeyHashMap};
    use crate::compat::{
        eprintln,
        rc::{Rc, Weak},
        String, Vec,
    };

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
}
