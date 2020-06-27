//! A hash map where the keys are held by weak pointers and compared by key value.

use std::borrow::Borrow;
use std::cmp::max;
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash, Hasher};
use std::fmt::{self, Debug, Formatter};
use std::mem;

use super::*;
use super::size_policy::*;
use super::traits::*;
use super::util::*;

pub use super::WeakKeyHashMap;

/// Represents an entry in the table which may be occupied or vacant.
pub enum Entry<'a, K: 'a + WeakKey, V: 'a> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

/// An occupied entry, which can be removed or viewed.
pub struct OccupiedEntry<'a, K: 'a + WeakKey, V: 'a>(InnerEntry<'a, K, V>);

/// A vacant entry, which can be inserted in or viewed.
pub struct VacantEntry<'a, K: 'a + WeakKey, V: 'a>(InnerEntry<'a, K, V>);

struct InnerEntry<'a, K: 'a + WeakKey, V: 'a> {
    map:        &'a mut WeakKeyInnerMap<K, V>,
    pos:        usize,
    key:        K::Strong,
    hash_code:  HashCode,
}

/// An iterator over the keys and values of the weak hash map.
#[derive(Clone, Debug)]
pub struct Iter<'a, K: 'a, V: 'a> {
    base: ::std::slice::Iter<'a, Bucket<K, V>>,
    size: usize,
}

impl<'a, K: WeakElement, V> Iterator for Iter<'a, K, V> {
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

#[derive(Debug)]
/// An iterator over the keys and mutable values of the weak hash map.
pub struct IterMut<'a, K: 'a, V: 'a> {
    base: ::std::slice::IterMut<'a, Bucket<K, V>>,
    size: usize,
}

impl<'a, K: WeakElement, V> Iterator for IterMut<'a, K, V> {
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
pub struct Drain<'a, K: 'a, V: 'a> {
    base: ::std::slice::IterMut<'a, Bucket<K, V>>,
    size: usize,
}

impl<'a, K: WeakElement, V> Iterator for Drain<'a, K, V> {
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
            *option = None;
        }
    }
}

/// An iterator that consumes the values of a weak hash map, leaving it empty.
pub struct IntoIter<K, V> {
    base: ::std::vec::IntoIter<Bucket<K, V>>,
    size: usize,
}

impl<K: WeakElement, V> Iterator for IntoIter<K, V> {
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
    /// Creates an empty `WeakKeyHashMap`.
    pub fn new() -> Self {
        Self::with_capacity(DEFAULT_INITIAL_CAPACITY)
    }

    /// Creates an empty `WeakKeyHashMap` with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, Default::default())
    }
}

impl<K: WeakKey, V, S: BuildHasher> WeakKeyHashMap<K, V, S>
{
    /// Creates an empty `WeakKeyHashMap` with the given capacity and hasher.
    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_capacity_and_hasher(DEFAULT_INITIAL_CAPACITY, hash_builder)
    }

    /// Creates an empty `WeakKeyHashMap` with the given capacity and hasher.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        WeakKeyHashMap {
            hash_builder,
            inner: WeakKeyInnerMap {
                buckets: new_boxed_option_slice(capacity),
                len: 0,
            }
        }
    }

    /// Returns a reference to the map's `BuildHasher`.
    pub fn hasher(&self) -> &S {
        &self.hash_builder
    }

    /// Returns the number of elements the map can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// This has some preconditions.
    fn resize(&mut self, capacity: usize) {
        let old_buckets = mem::replace(&mut self.inner.buckets,
                                       new_boxed_option_slice(capacity));

        let iter = IntoIter {
            base: old_buckets.into_vec().into_iter(),
            size: self.inner.len,
        };

        self.inner.len = 0;

        for (key, value) in iter {
            self.entry_no_grow(key).or_insert(value);
        }
    }

    /// Removes all mappings whose keys have expired.
    pub fn remove_expired(&mut self) {
        self.retain(|_, _| true)
    }

    /// Reserves room for additional elements.
    pub fn reserve(&mut self, additional_capacity: usize) {
        let new_capacity = additional_capacity + self.capacity();
        self.resize(new_capacity);
    }

    /// Shrinks the capacity to the minimum allowed to hold the current number of elements.
    pub fn shrink_to_fit(&mut self) {
        self.remove_expired();
        let new_capacity = (self.len() as f32 / COLLECT_LOAD_FACTOR).ceil() as usize;
        self.resize(new_capacity);
    }

    /// Returns an over-approximation of the number of elements.
    pub fn len(&self) -> usize {
        self.inner.len
    }

    /// Is the map empty?
    ///
    /// Note that this may return false even if all keys in the map have
    /// expired, if they haven't been collected yet.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The proportion of buckets that are used.
    ///
    /// This is an over-approximation because of expired keys.
    pub fn load_factor(&self) -> f32 {
        (self.len() as f32 + 1.0) / self.capacity() as f32
    }

    fn maybe_adjust_size(&mut self) {
        if self.load_factor() > COLLECT_LOAD_FACTOR {
            self.remove_expired();

            let load_factor = self.load_factor();
            let capacity = self.capacity();
            if load_factor > GROW_LOAD_FACTOR {
                self.resize(max(1, capacity * 2));
            } else if load_factor < SHRINK_LOAD_FACTOR && capacity > DEFAULT_INITIAL_CAPACITY {
                self.resize(max(1, capacity / 2));
            }
        }
    }

    /// Gets the requested entry.
    pub fn entry(&mut self, key: K::Strong) -> Entry<K, V> {
        self.maybe_adjust_size();
        self.entry_no_grow(key)
    }

    fn entry_no_grow(&mut self, key: K::Strong) -> Entry<K, V> {
        let mut inner = {
            let hash_code = K::with_key(&key, |k| self.hash(k));
            InnerEntry {
                pos:        self.which_bucket(hash_code),
                map:        &mut self.inner,
                hash_code,
                key,
            }
        };

        for dist in 0 .. inner.capacity() {
            match inner.bucket_status() {
                BucketStatus::Unoccupied =>
                    return Entry::Vacant(VacantEntry(inner)),
                BucketStatus::MatchesKey =>
                    return Entry::Occupied(OccupiedEntry(inner)),
                BucketStatus::ProbeDistance(bucket_distance) => {
                    if bucket_distance < dist {
                        return Entry::Vacant(VacantEntry(inner))
                    } else {
                        inner.pos = inner.next_bucket(inner.pos);
                    }
                }
            }
        }

        panic!("WeakKeyHashTable::entry: out of space");
    }

    /// Removes all associations from the map.
    pub fn clear(&mut self) {
        self.drain();
    }

    fn find_bucket<Q>(&self, key: &Q) -> Option<(usize, K::Strong, HashCode)>
        where Q: ?Sized + Hash + Eq,
              K::Key: Borrow<Q>
    {
        if self.capacity() == 0 { return None; }

        let hash_code = self.hash(key);
        let mut pos = self.which_bucket(hash_code);

        for dist in 0 .. self.capacity() {
            if let Some((ref weak_key, _, bucket_hash_code)) = self.inner.buckets[pos] {
                if bucket_hash_code == hash_code {
                    if let Some(bucket_key) = weak_key.view() {
                        if K::with_key(&bucket_key, |k| k.borrow() == key) {
                            return Some((pos, bucket_key, bucket_hash_code));
                        }
                    }
                }

                let bucket_dist =
                    self.probe_distance(pos, self.which_bucket(bucket_hash_code));
                if bucket_dist < dist {
                    return None;
                }
            } else {
                return None;
            }

            pos = self.next_bucket(pos);
        }

        None
    }

    /// Returns a reference to the value corresponding to the key.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
        where Q: ?Sized + Hash + Eq,
              K::Key: Borrow<Q>
    {
        self.find_bucket(key).and_then(move |tup|
            self.inner.buckets[tup.0].as_ref().map(|bucket| &bucket.1))
    }

    /// Returns true if the map contains the specified key.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
        where Q: ?Sized + Hash + Eq,
              K::Key: Borrow<Q>
    {
        self.find_bucket(key).is_some()
    }

    /// Returns a strong reference to the key, if found.
    pub fn get_key<Q>(&self, key: &Q) -> Option<K::Strong>
        where Q: ?Sized + Hash + Eq,
              K::Key: Borrow<Q>
    {
        self.find_bucket(key).map(|tup| tup.1)
    }

    /// Returns a pair of a strong reference to the key, and a reference to the value, if present.
    pub fn get_both<Q>(&self, key: &Q) -> Option<(K::Strong, &V)>
        where Q: ?Sized + Hash + Eq,
              K::Key: Borrow<Q>
    {
        self.find_bucket(key).and_then(move |tup|
            self.inner.buckets[tup.0].as_ref().map(|bucket| (tup.1, &bucket.1)))
    }

    /// Returns a mutable reference to the value corresponding to the key.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
        where Q: ?Sized + Hash + Eq,
              K::Key: Borrow<Q>
    {
        self.find_bucket(key).and_then(move |tup|
            self.inner.buckets[tup.0].as_mut().map(|bucket| &mut bucket.1))
    }

    /// Returns a pair of a strong reference to the key, and a mutable reference to the value,
    /// if present.
    pub fn get_both_mut<Q>(&mut self, key: &Q) -> Option<(K::Strong, &mut V)>
        where Q: ?Sized + Hash + Eq,
              K::Key: Borrow<Q>
    {
        self.find_bucket(key).and_then(move |tup|
            self.inner.buckets[tup.0].as_mut().map(|bucket| (tup.1, &mut bucket.1)))
    }

    /// Unconditionally inserts the value, returning the old value if already present.
    ///
    /// Unlike `std::collections::HashMap`, this replaced the key even if occupied.
    pub fn insert(&mut self, key: K::Strong, value: V) -> Option<V> {
        match self.entry(key) {
            Entry::Occupied(mut occupied) => {
                Some(occupied.insert(value))
            },
            Entry::Vacant(vacant) => {
                vacant.insert(value);
                None
            }
        }
    }

    /// Removes the entry with the given key, if it exists, and returns the value.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
        where Q: ?Sized + Hash + Eq,
              K::Key: Borrow<Q>
    {
        self.find_bucket(key).map(|(pos, strong_key, hash_code)| {
            OccupiedEntry(InnerEntry {
                map:        &mut self.inner,
                pos,
                key:        strong_key,
                hash_code,
            }).remove()
        })
    }

    /// Removes all mappings not satisfying the given predicate.
    ///
    /// Also removes any expired mappings.
    pub fn retain<F>(&mut self, mut f: F)
        where F: FnMut(K::Strong, &mut V) -> bool
    {
        for i in 0 .. self.capacity() {
            let remove = match self.inner.buckets[i] {
                None => false,
                Some(ref mut bucket) =>
                    match bucket.0.view() {
                        None => true,
                        Some(key) => !f(key, &mut bucket.1),
                    }
            };

            if remove {
                self.inner.remove_index(i);
            }
        }
    }

    /// Is this map a submap of the other, using the given value comparison.
    ///
    /// In particular, all the keys of `self` must be in `other` and the values must compare
    /// `true` with `value_equal`.
    pub fn is_submap_with<F, S1, V1>(&self, other: &WeakKeyHashMap<K, V1, S1>,
                                     mut value_equal: F) -> bool
        where F: FnMut(&V, &V1) -> bool,
              S1: BuildHasher
    {
        for (key, value1) in self {
            if let Some(value2) = K::with_key(&key, |k| other.get(k)) {
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
    pub fn is_submap<V1, S1>(&self, other: &WeakKeyHashMap<K, V1, S1>) -> bool
        where V: PartialEq<V1>,
              S1: BuildHasher
    {
        self.is_submap_with(other, PartialEq::eq)
    }

    /// Are the keys of `self` a subset of the keys of `other`?
    pub fn domain_is_subset<V1, S1>(&self, other: &WeakKeyHashMap<K, V1, S1>) -> bool
        where S1: BuildHasher
    {
        self.is_submap_with(other, |_, _| true)
    }

    fn hash<Q>(&self, key: &Q) -> HashCode
        where Q: ?Sized + Hash,
              K::Key: Borrow<Q>
    {
        let mut hasher = self.hash_builder.build_hasher();
        key.hash(&mut hasher);
        HashCode(hasher.finish())
    }
}

impl<K, V, V1, S, S1> PartialEq<WeakKeyHashMap<K, V1, S1>> for WeakKeyHashMap<K, V, S>
    where K: WeakKey,
          V: PartialEq<V1>,
          S: BuildHasher,
          S1: BuildHasher
{
    fn eq(&self, other: &WeakKeyHashMap<K, V1, S1>) -> bool {
        self.is_submap(other) && other.domain_is_subset(self)
    }
}

impl<K: WeakKey, V: Eq, S: BuildHasher> Eq for WeakKeyHashMap<K, V, S> { }

impl<K: WeakKey, V, S: BuildHasher + Default> Default for WeakKeyHashMap<K, V, S> {
    fn default() -> Self {
        WeakKeyHashMap::with_hasher(Default::default())
    }
}

impl<'a, K, V, S, Q> ::std::ops::Index<&'a Q> for WeakKeyHashMap<K, V, S>
    where K: WeakKey,
          K::Key: Borrow<Q>,
          S: BuildHasher,
          Q: ?Sized + Eq + Hash
{
    type Output = V;

    fn index(&self, index: &'a Q) -> &Self::Output {
        self.get(index).expect("Index::index: key not found")
    }
}

impl<'a, K, V, S, Q> ::std::ops::IndexMut<&'a Q> for WeakKeyHashMap<K, V, S>
    where K: WeakKey,
          K::Key: Borrow<Q>,
          S: BuildHasher,
          Q: ?Sized + Eq + Hash
{
    fn index_mut(&mut self, index: &'a Q) -> &mut Self::Output {
        self.get_mut(index).expect("IndexMut::index_mut: key not found")
    }
}

impl<K, V, S> ::std::iter::FromIterator<(K::Strong, V)> for WeakKeyHashMap<K, V, S>
    where K: WeakKey,
          S: BuildHasher + Default
{
    fn from_iter<T: IntoIterator<Item=(K::Strong, V)>>(iter: T) -> Self {
        let mut result = WeakKeyHashMap::with_hasher(Default::default());
        result.extend(iter);
        result
    }
}

impl<K, V, S> ::std::iter::Extend<(K::Strong, V)> for WeakKeyHashMap<K, V, S>
    where K: WeakKey,
          S: BuildHasher
{
    fn extend<T: IntoIterator<Item=(K::Strong, V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

impl<'a, K, V, S> ::std::iter::Extend<(&'a K::Strong, &'a V)> for WeakKeyHashMap<K, V, S>
    where K: 'a + WeakKey,
          K::Strong: Clone,
          V: 'a + Clone,
          S: BuildHasher
{
    fn extend<T: IntoIterator<Item=(&'a K::Strong, &'a V)>>(&mut self, iter: T) {
        for (key, value) in iter {
            self.insert(key.clone(), value.clone());
        }
    }
}

enum BucketStatus {
    Unoccupied,
    MatchesKey,
    ProbeDistance(usize),
}

impl<'a, K: WeakKey, V> InnerEntry<'a, K, V> {
    // Gets the status of the current bucket.
    fn bucket_status(&self) -> BucketStatus {
        match &self.map.buckets[self.pos] {
            Some(bucket) => {
                if bucket.2 == self.hash_code {
                    if let Some(key) = bucket.0.view() {
                        if K::with_key(&self.key, |k1| K::with_key(&key, |k2| k1 == k2)) {
                            return BucketStatus::MatchesKey;
                        }
                    }
                }

                let dist = self.probe_distance(self.pos,
                                               self.which_bucket(bucket.2));
                BucketStatus::ProbeDistance(dist)
            },
            None => BucketStatus::Unoccupied,
        }
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

    /// Takes ownership of the key and value from the map.
    pub fn remove_entry(self) -> (K::Strong, V) {
        let (_, value, _) = self.0.map.buckets[self.0.pos].take().unwrap();
        self.0.map.remove_index(self.0.pos);
        (self.0.key, value)
    }

    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &V {
        &self.0.map.buckets[self.0.pos].as_ref().unwrap().1
    }

    /// Gets a mutable reference to the value in the entry.
    pub fn get_mut(&mut self) -> &mut V {
        &mut self.0.map.buckets[self.0.pos].as_mut().unwrap().1
    }

    /// Turns the entry into a mutable reference to the value borrowed from the map.
    pub fn into_mut(self) -> &'a mut V {
        &mut self.0.map.buckets[self.0.pos].as_mut().unwrap().1
    }

    /// Replaces the value in the entry with the given value.
    pub fn insert(&mut self, mut value: V) -> V {
        self.0.map.buckets[self.0.pos].as_mut().unwrap().0 = K::new(&self.0.key);
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
        let old_bucket = mem::replace(
            &mut self.0.map.buckets[self.0.pos],
            Some((K::new(&self.0.key), value, self.0.hash_code)));

        if let Some(full_bucket) = old_bucket {
            let next_bucket = self.next_bucket(self.0.pos);
            self.0.map.steal(next_bucket, full_bucket);
        }

        self.0.map.len += 1;

        &mut self.0.map.buckets[self.0.pos].as_mut().unwrap().1
    }
}

impl<K: WeakKey, V> WeakKeyInnerMap<K, V> {
    // Steals buckets starting at `pos`, replacing them with `bucket`.
    fn steal(&mut self, mut pos: usize, mut bucket: FullBucket<K, V>) {
        let mut my_dist = self.probe_distance(pos, self.which_bucket(bucket.2));

        while let Some(hash_code) = self.buckets[pos].as_ref().and_then(
            |bucket| if bucket.0.is_expired() {None} else {Some(bucket.2)}) {

            let victim_dist = self.probe_distance(pos, self.which_bucket(hash_code));

            if my_dist > victim_dist {
                mem::swap(self.buckets[pos].as_mut().unwrap(), &mut bucket);
                my_dist = victim_dist;
            }

            pos = self.next_bucket(pos);
            my_dist += 1;
        }

        self.buckets[pos] = Some(bucket);
    }

    /// Removes the element at `dst`, shifting if necessary to preserve invariants.
    fn remove_index(&mut self, mut dst: usize) {
        let mut src = self.next_bucket(dst);

        // We are going to remove the buckets in the range [dst, src)

        loop {
            let hash_code_option = self.buckets[src].as_ref().map(|tup| tup.2);

            if let Some(hash_code) = hash_code_option {
                let goal_pos = self.which_bucket(hash_code);
                let dist = self.probe_distance(src, goal_pos);
                if dist == 0 { break; }

                if !self.buckets[src].as_ref().unwrap().0.is_expired() {
                    if in_interval(dst, goal_pos, src) {
                        self.erase_range(dst, goal_pos);
                        self.buckets[goal_pos] = self.buckets[src].take();
                        dst = self.next_bucket(goal_pos);
                    } else {
                        self.buckets[dst] = self.buckets[src].take();
                        dst = self.next_bucket(dst);
                    }
                }
            } else {
                break;
            }

            src = self.next_bucket(src);
        }

        self.erase_range(dst, src);
    }

    /// Erases the (presumably expired, but not empty) elements in [start, limit).
    fn erase_range(&mut self, mut start: usize, limit: usize)
    {
        while start != limit {
            self.buckets[start] = None;
            self.len -= 1;
            start = self.next_bucket(start);
        }
    }
}

// Is value in [start, limit) modulo capacity?
fn in_interval(start: usize, value: usize, limit: usize) -> bool
{
    if start <= limit {
        start <= value && value < limit
    } else {
        start <= value || value < limit
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
        assert_ne!( self.capacity(), 0 );
        (pos + 1) % self.capacity()
    }

    fn which_bucket(&self, hash_code: HashCode) -> usize {
        assert_ne!( self.capacity(), 0 );
        (hash_code.0 as usize) % self.capacity()
    }
}

impl<K, V> ModuloCapacity for WeakKeyInnerMap<K, V> {
    fn capacity(&self) -> usize {
        self.buckets.len()
    }
}

impl<K, V, S> ModuloCapacity for WeakKeyHashMap<K, V, S> {
    fn capacity(&self) -> usize {
        self.inner.capacity()
    }
}

impl<'a, K: WeakKey, V> ModuloCapacity for InnerEntry<'a, K, V> {
    fn capacity(&self) -> usize {
        self.map.capacity()
    }
}

impl<'a, K: WeakKey, V> ModuloCapacity for OccupiedEntry<'a, K, V> {
    fn capacity(&self) -> usize {
        self.0.capacity()
    }
}

impl<'a, K: WeakKey, V> ModuloCapacity for VacantEntry<'a, K, V> {
    fn capacity(&self) -> usize {
        self.0.capacity()
    }
}

impl<K, V> Debug for WeakKeyInnerMap<K, V>
    where K: WeakElement,
          K::Strong: Debug,
          V: Debug
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{{ ")?;
        for (i, bucket) in self.buckets.iter().enumerate() {
            if let Some((ref k, ref v, _)) = *bucket {
                write!(f, "[{}] {:?} => {:?}, ", i, k.view(), *v)?;
            }
        }
        write!(f, "}}")
    }
}

impl<K: WeakElement, V: Debug, S> Debug for WeakKeyHashMap<K, V, S>
    where K::Strong: Debug
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, K: WeakKey, V: Debug> Debug for Entry<'a, K, V>
    where K::Strong: Debug
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            Entry::Occupied(ref e)  => e.fmt(f),
            Entry::Vacant(ref e)    => e.fmt(f),
        }
    }
}

impl<'a, K: WeakKey, V: Debug> Debug for OccupiedEntry<'a, K, V>
    where K::Strong: Debug
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a, K: WeakKey, V: Debug> Debug for VacantEntry<'a, K, V>
    where K::Strong: Debug
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<'a, K: WeakKey, V: Debug> Debug for InnerEntry<'a, K, V>
    where K::Strong: Debug
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "InnerEntry {{ pos = {}, buckets = {:?} }}", self.pos, self.map)
    }
}

impl<K: WeakElement, V, S> IntoIterator for WeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            size: self.inner.len,
            base: self.inner.buckets.into_vec().into_iter(),
        }
    }
}

impl<'a, K: WeakElement, V, S> IntoIterator for &'a WeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            base: self.inner.buckets.iter(),
            size: self.inner.len,
        }
    }
}

impl<'a, K: WeakElement, V, S> IntoIterator for &'a mut WeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IterMut {
            base: self.inner.buckets.iter_mut(),
            size: self.inner.len,
        }
    }
}

impl<K: WeakElement, V, S> WeakKeyHashMap<K, V, S> {
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

    /// Gets an iterator over the keys and mutable values.
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        self.into_iter()
    }

    /// Gets an iterator over the mutable values.
    pub fn values_mut(&mut self) -> ValuesMut<K, V> {
        ValuesMut(self.iter_mut())
    }

    /// Gets a draining iterator, which removes all the values but retains the storage.
    pub fn drain(&mut self) -> Drain<K, V> {
        let old_len = self.inner.len;
        self.inner.len = 0;
        Drain {
            base: self.inner.buckets.iter_mut(),
            size: old_len,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::{Rc, Weak};
    use super::{Entry, WeakKeyHashMap};

    #[test]
    fn simple() {
        let mut map: WeakKeyHashMap<Weak<str>, usize> = WeakKeyHashMap::new();
        assert_eq!( map.len(), 0 );
        assert!( !map.contains_key("five") );

        let five: Rc<str> = Rc::from("five".to_string());
        map.insert(five.clone(), 5);

        assert_eq!( map.len(), 1 );
        assert!( map.contains_key("five") );

        drop(five);

        assert_eq!( map.len(), 1 );
        assert!( !map.contains_key("five") );

        map.remove_expired();

        assert_eq!( map.len(), 0 );
        assert!( !map.contains_key("five") );
    }

    // From https://github.com/tov/weak-table-rs/issues/1#issuecomment-461858060
    #[test]
    fn insert_and_check() {
        let mut rcs: Vec<Rc<u32>> = Vec::new();

        for i in 0 .. 50 {
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

        assert_eq!( count, rcs.len() );
    }
}
