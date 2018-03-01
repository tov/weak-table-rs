use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash, Hasher};
use std::fmt::{self, Debug, Formatter};
use std::mem;

use super::traits::*;
use super::util::*;

const DEFAULT_INITIAL_CAPACITY: usize = 8;

type Bucket<K, V> = Option<(K, V, u64)>;
type TablePtr<K, V> = Box<[Bucket<K, V>]>;

/// A mapping from weak pointers to values.
///
/// When a weak pointer expires, its mapping is lazily removed.
#[derive(Clone)]
pub struct WeakKeyHashMap<K, V, S = RandomState> {
    hash_builder: S,
    buckets: TablePtr<K, V>,
    len: usize,
}

/// Represents an entry in the table which may be occupied or vacant.
#[derive(Debug)]
pub enum Entry<'a, K: 'a + WeakKey, V: 'a> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

/// An occupied entry, which can be removed or viewed.
#[derive(Debug)]
pub struct OccupiedEntry<'a, K: 'a + WeakKey, V: 'a>(InnerEntry<'a, K, V>);

/// A vacant entry, which can be inserted in or viewed.
#[derive(Debug)]
pub struct VacantEntry<'a, K: 'a + WeakKey, V: 'a>(InnerEntry<'a, K, V>);

struct InnerEntry<'a, K: 'a + WeakKey, V: 'a> {
    buckets: &'a mut TablePtr<K, V>,
    len: &'a mut usize,
    pos: usize,
    key: K::Strong,
    hash_code: u64,
}

/// An iterator over the keys and values of the weak hash map.
#[derive(Clone)]
pub struct Iter<'a, K: 'a, V: 'a> {
    base: ::std::slice::Iter<'a, Bucket<K, V>>,
    size: usize,
}

impl<'a, K: WeakKey, V> Iterator for Iter<'a, K, V> {
    type Item = (K::Strong, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(bucket) = self.base.next() {
            if let Some((ref weak_ptr, ref value, _)) = *bucket {
                self.size -= 1;
                if let Some(strong_ptr) = weak_ptr.view() {
                    return Some((strong_ptr, value));
                }
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.size))
    }
}

/// An iterator over the keys and mutable values of the weak hash map.
pub struct IterMut<'a, K: 'a, V: 'a> {
    base: ::std::slice::IterMut<'a, Bucket<K, V>>,
    size: usize,
}

impl<'a, K: WeakKey, V> Iterator for IterMut<'a, K, V> {
    type Item = (K::Strong, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(bucket) = self.base.next() {
            if let Some((ref weak_ptr, ref mut value, _)) = *bucket {
                self.size -= 1;
                if let Some(strong_ptr) = weak_ptr.view() {
                    return Some((strong_ptr, value));
                }
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.size))
    }
}

/// An iterator over the keys of the weak hash map.
#[derive(Clone)]
pub struct Keys<'a, K: 'a, V: 'a>(Iter<'a, K, V>);

impl<'a, K: WeakKey, V> Iterator for Keys<'a, K, V> {
    type Item = K::Strong;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

/// An iterator over the values of the weak hash map.
#[derive(Clone)]
pub struct Values<'a, K: 'a, V: 'a>(Iter<'a, K, V>);

impl<'a, K: WeakKey, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

/// An iterator over the mutable values of the weak hash map.
pub struct ValuesMut<'a, K: 'a, V: 'a>(IterMut<'a, K, V>);

impl<'a, K: WeakKey, V> Iterator for ValuesMut<'a, K, V> {
    type Item = &'a mut V;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, v)| v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

/// An iterator that consumes the values of a weak hash map, leaving it empty.
pub struct Drain<'a, K: 'a, V: 'a> {
    base: ::std::slice::IterMut<'a, Bucket<K, V>>,
    size: usize,
}

impl<'a, K: WeakKey, V> Iterator for Drain<'a, K, V> {
    type Item = (K::Strong, V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(bucket) = self.base.next() {
            if let Some((weak_ptr, value, _)) = bucket.take() {
                self.size -= 1;
                if let Some(strong_ptr) = weak_ptr.view() {
                    return Some((strong_ptr, value));
                }
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.size))
    }
}

impl<'a, K, V> Drop for Drain<'a, K, V> {
    fn drop(&mut self) {
        while let Some(option) = self.base.next() {
            option.take();
        }
    }
}

/// An iterator that consumes the values of a weak hash map, leaving it empty.
pub struct IntoIter<K, V> {
    base: ::std::vec::IntoIter<Bucket<K, V>>,
    size: usize,
}

impl<K: WeakKey, V> Iterator for IntoIter<K, V> {
    type Item = (K::Strong, V);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(bucket) = self.base.next() {
            if let Some((weak_ptr, value, _)) = bucket {
                self.size -= 1;
                if let Some(strong_ptr) = weak_ptr.view() {
                    return Some((strong_ptr, value));
                }
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.size))
    }
}

impl<K: WeakKey, V> WeakKeyHashMap<K, V, RandomState>
{
    /// Creates an empty `WeakHashmap`.
    pub fn new() -> Self {
        Self::with_capacity(DEFAULT_INITIAL_CAPACITY)
    }

    /// Creates an empty `WeakHashmap` with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, Default::default())
    }
}

impl<K: WeakKey, V, S: BuildHasher> WeakKeyHashMap<K, V, S>
{
    /// Creates an empty `WeakHashMap` with the given capacity and hasher.
    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_capacity_and_hasher(DEFAULT_INITIAL_CAPACITY, hash_builder)
    }

    /// Creates an empty `WeakHashMap` with the given capacity and hasher.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        WeakKeyHashMap {
            hash_builder: hash_builder,
            buckets: new_boxed_option_slice(capacity),
            len: 0,
        }
    }

    /// Returns a reference to the map's `BuildHasher`.
    pub fn hasher(&self) -> &S {
        &self.hash_builder
    }

    /// Returns the number of elements the map can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.buckets.len()
    }

    /// This has some preconditions.
    fn resize(&mut self, capacity: usize) {
        let mut old_buckets = new_boxed_option_slice(capacity);
        mem::swap(&mut self.buckets, &mut old_buckets);

        let mut iter = IntoIter {
            base: old_buckets.into_vec().into_iter(),
            size: self.len,
        };

        for (key, value) in iter {
            self.entry(key).or_insert(value);
        }
    }

    /// Returns an over-approximation of the number of elements.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Gets the requested entry.
    pub fn entry(&mut self, key: K::Strong) -> Entry<K, V> {
        enum BucketStatus {
            Unoccupied,
            MatchesKey,
            ProbeDistance(usize),
        }

        let mut inner = {
            let hash_code = self.hash(K::view_key(&key));
            InnerEntry {
                pos:        self.which_bucket(hash_code),
                buckets:    &mut self.buckets,
                len:        &mut self.len,
                hash_code,
                key,
            }
        };
        let mut dist = 0usize;

        loop {
            let status = match inner.buckets[inner.pos] {
                Some((ref weak_key, _, hash_code)) => match weak_key.view() {
                    Some(key) => if K::view_key(&inner.key) == K::view_key(&key) {
                        BucketStatus::MatchesKey
                    } else {
                        let dist = inner.probe_distance(inner.pos,
                                                       inner.which_bucket(hash_code));
                        BucketStatus::ProbeDistance(dist)
                    },
                    None => BucketStatus::Unoccupied,
                },
                None => BucketStatus::Unoccupied,
            };

            match status {
                BucketStatus::Unoccupied =>
                    return Entry::Vacant(VacantEntry(inner)),
                BucketStatus::MatchesKey =>
                    return Entry::Occupied(OccupiedEntry(inner)),
                BucketStatus::ProbeDistance(bucket_distance) => {
                    if bucket_distance > dist {
                        return Entry::Vacant(VacantEntry(inner))
                    } else {
                        dist += 1;
                        inner.pos = inner.next_bucket(inner.pos);
                    }
                }
            }
        }
    }

    /// Removes all associations from the map.
    pub fn clear(&mut self) {
        for _ in self.drain() { }
    }

    pub fn get<Q: ?Sized + Hash + Eq>(&self, key: &Q) -> Option<&V>
        where K::Key: Borrow<Q>
    {
        unimplemented!();
    }

    /// Unconditionally inserts the value, returning the old value if already present. Does not
    /// replace the key.
    pub fn insert(&mut self, key: K::Strong, value: V) -> Option<V> {
        match self.entry(key) {
            Entry::Occupied(mut occupied) => Some(occupied.insert(value)),
            Entry::Vacant(mut vacant) => {
                vacant.insert(value);
                None
            }
        }
    }

    fn hash(&self, key: &K::Key) -> u64 {
        let mut hasher = self.hash_builder.build_hasher();
        key.hash(&mut hasher);
        hasher.finish()
    }
}

impl<'a, K: WeakKey, V> Entry<'a, K, V> {
    /// Ensures a value is in the entry by inserting a default value
    /// if empty, and returns a mutable reference to the value in the
    /// entry.
    pub fn or_insert(self, default: V) -> &'a mut V {
        self.or_insert_with(|| default)
    }

    /// Ensures a value is in the entry by inserting the result of the
    /// default function if empty, and returns a mutable reference to
    /// the value in the entry.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(occupied) => occupied.into_mut(),
            Entry::Vacant(vacant) => vacant.insert(default()),
        }
    }

    /// Returns a reference to this entry's key.
    pub fn key(&self) -> &K::Strong {
        match *self {
            Entry::Occupied(ref occupied) => occupied.key(),
            Entry::Vacant(ref vacant) => vacant.key(),
        }
    }
}

impl<'a, K: WeakKey, V> OccupiedEntry<'a, K, V> {
    /// Gets a reference to the key held by the entry.
    pub fn key(&self) -> &K::Strong {
        &self.0.key
    }

    fn erase_index(&mut self, index: usize) {
        self.0.buckets[index] = None;
        *self.0.len -= 1;
    }

    /// Takes ownership of the key and value from the map.
    pub fn remove_entry(self) -> (K, V) {
        unimplemented!();
    }

    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &V {
        &self.0.buckets[self.0.pos].as_ref().unwrap().1
    }

    /// Gets a mutable reference to the value in the entry.
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.0.buckets[self.0.pos].as_mut().unwrap().1
    }

    /// Turns the entry into a mutable reference to the value borrowed from the map.
    pub fn into_mut(self) -> &'a mut V {
        &mut self.0.buckets[self.0.pos].as_mut().unwrap().1
    }

    /// Replaces the value in the entry with the given value.
    pub fn insert(&mut self, mut value: V) -> V {
        mem::swap(self.get_mut(), &mut value);
        value
    }

    /// Removes the entry, returning the value.
    pub fn remove(self) -> V {
        self.remove_entry().1
    }
}

impl<'a, K: WeakKey, V> VacantEntry<'a, K, V> {
    /// Gets a reference to the key that would be used when inserting a
    /// value through the `VacantEntry`.
    pub fn key(&self) -> &K::Strong {
        &self.0.key
    }

    /// Returns ownership of the key.
    pub fn into_key(self) -> K::Strong {
        self.0.key
    }

    /// Inserts the key and value into the map and return a mutable
    /// reference to the value.
    pub fn insert(self, value: V) -> &'a mut V {
        unimplemented!()
    }
}

// Helper trait for computing with indices modulo capacity.
trait ModuloCapacity {
    fn capacity(&self) -> usize;

    fn probe_distance(&self, actual: usize, ideal: usize) -> usize {
        if actual >= ideal {
            actual - ideal
        } else {
            actual + self.capacity() - ideal
        }
    }

    fn next_bucket(&self, pos: usize) -> usize {
        (pos + 1) % self.capacity()
    }

    fn which_bucket(&self, hash_code: u64) -> usize {
        hash_code as usize % self.capacity()
    }
}

impl<K, V, S> ModuloCapacity for WeakKeyHashMap<K, V, S> {
    fn capacity(&self) -> usize {
        self.buckets.len()
    }
}

impl<'a, K: WeakKey, V> ModuloCapacity for InnerEntry<'a, K, V> {
    fn capacity(&self) -> usize {
        self.buckets.len()
    }
}

fn debug_table<K: Debug, V: Debug>(buckets: &TablePtr<K, V>, f: &mut Formatter) -> fmt::Result {
    write!(f, "{{ ")?;
    for (i, bucket) in buckets.iter().enumerate() {
        if let &Some((ref k, ref v, hc)) = bucket {
            write!(f, "[{}] {:?} => {:?} ({:x}), ", i, *k, *v, hc)?;
        }
    }
    write!(f, "}}")
}

impl<K: Debug, V: Debug, S> Debug for WeakKeyHashMap<K, V, S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        debug_table(&self.buckets, f)
    }
}

impl<'a, K: WeakKey + Debug, V: Debug> Debug for InnerEntry<'a, K, V> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "InnerEntry {{ pos = {}, buckets = ", self.pos)?;
        debug_table(&self.buckets, f)?;
        write!(f, " }}")
    }
}

impl<K: WeakKey, V, S> IntoIterator for WeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            size: self.len,
            base: self.buckets.into_vec().into_iter(),
        }
    }
}

impl<'a, K: WeakKey, V, S> IntoIterator for &'a WeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            base: self.buckets.iter(),
            size: self.len,
        }
    }
}

impl<'a, K: WeakKey, V, S> IntoIterator for &'a mut WeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IterMut {
            base: self.buckets.iter_mut(),
            size: self.len,
        }
    }
}

impl<K: WeakKey, V, S> WeakKeyHashMap<K, V, S> {
    /// Gets an iterator over the keys and values.
    pub fn iter(&self) -> Iter<K, V> {
        self.into_iter()
    }

    /// Gets an iterator over the keys.
    pub fn keys(&self) -> Keys<K, V> {
        Keys(self.iter())
    }

    /// Gets an iterator over the values.
    pub fn values(&self) -> Values<K, V> {
        Values(self.iter())
    }

    // Gets an iterator over the keys and mutable values.
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        self.into_iter()
    }

    /// Gets an iterator over the mutable values.
    pub fn values_mut(&mut self) -> ValuesMut<K, V> {
        ValuesMut(self.iter_mut())
    }

    /// Gets a draining iterator, which removes all the values but retains the storage.
    pub fn drain(&mut self) -> Drain<K, V> {
        let old_len = self.len;
        self.len = 0;
        Drain {
            base: self.buckets.iter_mut(),
            size: old_len,
        }
    }
}
