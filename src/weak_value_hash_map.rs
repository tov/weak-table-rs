//! A hash map where the values are held by weak pointers.

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

pub use super::WeakValueHashMap;

/// Represents an entry in the table which may be occupied or vacant.
pub enum Entry<'a, K: 'a, V: 'a + WeakElement> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

/// An occupied entry, which can be removed or viewed.
pub struct OccupiedEntry<'a, K: 'a, V: 'a + WeakElement> {
    inner: InnerEntry<'a, K, V>,
    value: V::Strong,
}

/// A vacant entry, which can be inserted in or viewed.
pub struct VacantEntry<'a, K: 'a, V: 'a + WeakElement> {
    inner: InnerEntry<'a, K, V>,
}

struct InnerEntry<'a, K: 'a, V: 'a + WeakElement> {
    map:        &'a mut WeakValueInnerMap<K, V>,
    pos:        usize,
    key:        K,
    hash_code:  HashCode,
}

/// An iterator over the keys and values of the weak hash map.
#[derive(Clone, Debug)]
pub struct Iter<'a, K: 'a, V: 'a> {
    base: ::std::slice::Iter<'a, Bucket<K, V>>,
    size: usize,
}

impl<'a, K, V: WeakElement> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, V::Strong);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(bucket) = self.base.next() {
            if let Some((ref key, ref weak_value, _)) = *bucket {
                self.size -= 1;
                if let Some(value) = weak_value.view() {
                    return Some((key, value));
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
pub struct Drain<'a, K: 'a, V: 'a> {
    base: ::std::slice::IterMut<'a, Bucket<K, V>>,
    size: usize,
}

impl<'a, K, V: WeakElement> Iterator for Drain<'a, K, V> {
    type Item = (K, V::Strong);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(bucket) = self.base.next() {
            if let Some((key, weak_value, _)) = bucket.take() {
                self.size -= 1;
                if let Some(value) = weak_value.view() {
                    return Some((key, value));
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

impl<K, V: WeakElement> Iterator for IntoIter<K, V> {
    type Item = (K, V::Strong);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(bucket) = self.base.next() {
            if let Some((key, weak_value, _)) = bucket {
                self.size -= 1;
                if let Some(value) = weak_value.view() {
                    return Some((key, value));
                }
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.size))
    }
}

impl<K: Eq + Hash, V: WeakElement> WeakValueHashMap<K, V, RandomState>
{
    /// Creates an empty `WeakValueHashMap`.
    pub fn new() -> Self {
        Self::with_capacity(DEFAULT_INITIAL_CAPACITY)
    }

    /// Creates an empty `WeakValueHashMap` with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, Default::default())
    }
}

impl<K: Eq + Hash, V: WeakElement, S: BuildHasher> WeakValueHashMap<K, V, S>
{
    /// Creates an empty `WeakValueHashMap` with the given capacity and hasher.
    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_capacity_and_hasher(DEFAULT_INITIAL_CAPACITY, hash_builder)
    }

    /// Creates an empty `WeakValueHashMap` with the given capacity and hasher.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        WeakValueHashMap {
            hash_builder,
            inner: WeakValueInnerMap {
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
    pub fn entry(&mut self, key: K) -> Entry<K, V> {
        self.maybe_adjust_size();
        self.entry_no_grow(key)
    }

    fn entry_no_grow(&mut self, key: K) -> Entry<K, V> {
        let mut inner = {
            let hash_code = self.hash(&key);
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
                    return Entry::Vacant(VacantEntry {inner}),
                BucketStatus::MatchesKey(value) => {
                    return Entry::Occupied(OccupiedEntry {inner, value})
                }
                BucketStatus::ProbeDistance(bucket_distance) => {
                    if bucket_distance < dist {
                        return Entry::Vacant(VacantEntry {inner})
                    } else {
                        inner.pos = inner.next_bucket(inner.pos);
                    }
                }
            }
        }

        panic!("WeakValueHashTable::entry: out of space");
    }

    /// Removes all associations from the map.
    pub fn clear(&mut self) {
        self.drain();
    }

    fn find_bucket<Q>(&self, key: &Q) -> Option<(usize, V::Strong)>
        where Q: ?Sized + Hash + Eq,
              K: Borrow<Q>
    {
        if self.capacity() == 0 { return None; }

        let hash_code = self.hash(key);
        let mut pos = self.which_bucket(hash_code);

        for dist in 0 .. self.capacity() {
            if let Some((ref bucket_key, ref weak_value, bucket_hash_code)) = self.inner.buckets[pos] {
                if bucket_hash_code == hash_code {
                    if let Some(value) = weak_value.view() {
                        if bucket_key.borrow() == key {
                            return Some((pos, value));
                        }
                    }
                }

                let bucket_dist =
                    self.probe_distance(pos, self.which_bucket(hash_code));
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
    pub fn get<Q>(&self, key: &Q) -> Option<V::Strong>
        where Q: ?Sized + Hash + Eq,
              K: Borrow<Q>
    {
        self.find_bucket(key).map(|tup| tup.1)
    }

    /// Returns true if the map contains the specified key.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
        where Q: ?Sized + Hash + Eq,
              K: Borrow<Q>
    {
        self.find_bucket(key).is_some()
    }

    /// Unconditionally inserts the value, returning the old value if already present.
    ///
    /// Like `std::collections::HashMap`, this does not replace the key if occupied.
    pub fn insert(&mut self, key: K, value: V::Strong) -> Option<V::Strong> {
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
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V::Strong>
        where Q: ?Sized + Hash + Eq,
              K: Borrow<Q>
    {
        if let Some((pos, value)) = self.find_bucket(key) {
            self.inner.remove_index(pos);
            Some(value)
        } else {
            None
        }
    }

    /// Removes all mappings not satisfying the given predicate.
    ///
    /// Also removes any expired mappings.
    pub fn retain<F>(&mut self, mut f: F)
        where F: FnMut(&K, V::Strong) -> bool
    {
        for i in 0 .. self.capacity() {
            let remove = match self.inner.buckets[i] {
                None => false,
                Some(ref mut bucket) =>
                    match bucket.1.view() {
                        None => true,
                        Some(value) => !f(&bucket.0, value),
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
    pub fn is_submap_with<F, S1, V1>(&self, other: &WeakValueHashMap<K, V1, S1>,
                                     mut value_equal: F) -> bool
        where V1: WeakElement,
              F: FnMut(V::Strong, V1::Strong) -> bool,
              S1: BuildHasher
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
    pub fn is_submap<V1, S1>(&self, other: &WeakValueHashMap<K, V1, S1>) -> bool
        where V1: WeakElement,
              V::Strong: PartialEq<V1::Strong>,
              S1: BuildHasher
    {
        self.is_submap_with(other, |v, v1| v == v1)
    }

    /// Are the keys of `self` a subset of the keys of `other`?
    pub fn domain_is_subset<V1, S1>(&self, other: &WeakValueHashMap<K, V1, S1>) -> bool
        where V1: WeakElement,
              S1: BuildHasher
    {
        self.is_submap_with(other, |_, _| true)
    }

    fn hash<Q>(&self, key: &Q) -> HashCode
        where Q: ?Sized + Hash,
              K: Borrow<Q>
    {
        let mut hasher = self.hash_builder.build_hasher();
        key.hash(&mut hasher);
        HashCode(hasher.finish())
    }
}

impl<K, V, V1, S, S1> PartialEq<WeakValueHashMap<K, V1, S1>> for WeakValueHashMap<K, V, S>
    where K: Eq + Hash,
          V: WeakElement,
          V1: WeakElement,
          V::Strong: PartialEq<V1::Strong>,
          S: BuildHasher,
          S1: BuildHasher
{
    fn eq(&self, other: &WeakValueHashMap<K, V1, S1>) -> bool {
        self.is_submap(other) && other.domain_is_subset(self)
    }
}

impl<K: Eq + Hash, V: WeakElement, S: BuildHasher> Eq for WeakValueHashMap<K, V, S>
    where V::Strong: Eq
{ }

impl<K: Eq + Hash, V: WeakElement, S: BuildHasher + Default> Default for WeakValueHashMap<K, V, S> {
    fn default() -> Self {
        WeakValueHashMap::with_hasher(Default::default())
    }
}

impl<K, V, S> ::std::iter::FromIterator<(K, V::Strong)> for WeakValueHashMap<K, V, S>
    where K: Eq + Hash,
          V: WeakElement,
          S: BuildHasher + Default
{
    fn from_iter<T: IntoIterator<Item=(K, V::Strong)>>(iter: T) -> Self {
        let mut result = WeakValueHashMap::with_hasher(Default::default());
        result.extend(iter);
        result
    }
}

impl<K, V, S> Extend<(K, V::Strong)> for WeakValueHashMap<K, V, S>
    where K: Eq + Hash,
          V: WeakElement,
          S: BuildHasher
{
    fn extend<T: IntoIterator<Item=(K, V::Strong)>>(&mut self, iter: T) {
        for (key, value) in iter {
            self.insert(key, value);
        }
    }
}

impl<'a, K, V, S> Extend<(&'a K, &'a V::Strong)> for WeakValueHashMap<K, V, S>
    where K: 'a + Eq + Hash + Clone,
          V: 'a + WeakElement,
          V::Strong: Clone,
          S: BuildHasher
{
    fn extend<T: IntoIterator<Item=(&'a K, &'a V::Strong)>>(&mut self, iter: T) {
        for (key, value) in iter {
            self.insert(key.clone(), value.clone());
        }
    }
}

enum BucketStatus<V: WeakElement> {
    Unoccupied,
    MatchesKey(V::Strong),
    ProbeDistance(usize),
}

impl<'a, K: Eq + Hash, V: WeakElement> InnerEntry<'a, K, V> {
    // Gets the status of the current bucket.
    fn bucket_status(&self) -> BucketStatus<V> {
        match &self.map.buckets[self.pos] {
            Some(bucket) => {
                if bucket.2 == self.hash_code {
                    if let Some(value) = bucket.1.view() {
                        if self.key == bucket.0 {
                            return BucketStatus::MatchesKey(value);
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

impl<'a, K, V: WeakElement> Entry<'a, K, V> {
    /// Ensures a value is in the entry by inserting a default value
    /// if empty.
    pub fn or_insert(self, default: V::Strong) -> V::Strong {
        self.or_insert_with(|| default)
    }

    /// Ensures a value is in the entry by inserting the result of the
    /// default function if empty.
    pub fn or_insert_with<F: FnOnce() -> V::Strong>(self, default: F) -> V::Strong {
        match self {
            Entry::Occupied(occupied) => occupied.get_strong(),
            Entry::Vacant(vacant) => vacant.insert(default()),
        }
    }

    /// Returns a reference to this entry's key.
    pub fn key(&self) -> &K {
        match *self {
            Entry::Occupied(ref occupied) => occupied.key(),
            Entry::Vacant(ref vacant) => vacant.key(),
        }
    }
}

impl<'a, K, V: WeakElement> OccupiedEntry<'a, K, V> {
    /// Gets a reference to the key held by the entry.
    pub fn key(&self) -> &K {
        &self.inner.key
    }

    /// Takes ownership of the key and value from the map.
    pub fn remove_entry(self) -> (K, V::Strong) {
        let (key, w_value, _) = self.inner.map.buckets[self.inner.pos].take().unwrap();
        let value = w_value.view().unwrap();
        self.inner.map.remove_index(self.inner.pos);
        (key, value)
    }

    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &V::Strong {
        &self.value
    }

    /// Gets a copy of the strong value reference stored in the entry.
    pub fn get_strong(&self) -> V::Strong {
        V::clone(&self.value)
    }

    /// Replaces the value in the entry with the given value, returning the old value.
    pub fn insert(&mut self, value: V::Strong) -> V::Strong {
        self.inner.map.buckets[self.inner.pos].as_mut().unwrap().1 = V::new(&value);
        mem::replace(&mut self.value, value)
    }

    /// Removes the entry, returning the value.
    pub fn remove(self) -> V::Strong {
        self.remove_entry().1
    }
}

impl<'a, K, V: WeakElement> VacantEntry<'a, K, V> {
    /// Gets a reference to the key that would be used when inserting a
    /// value through the `VacantEntry`.
    pub fn key(&self) -> &K {
        &self.inner.key
    }

    /// Returns ownership of the key.
    pub fn into_key(self) -> K {
        self.inner.key
    }

    /// Inserts the value into the map, returning the same value.
    pub fn insert(self, value: V::Strong) -> V::Strong {
        let InnerEntry { map, key, hash_code, pos } = self.inner;

        let old_bucket = mem::replace(
            &mut map.buckets[pos],
            Some((key, V::new(&value), hash_code)));

        if let Some(full_bucket) = old_bucket {
            let next_bucket = map.next_bucket(pos);
            map.steal(next_bucket, full_bucket);
        }

        map.len += 1;

        value
    }
}

impl<K, V: WeakElement> WeakValueInnerMap<K, V> {
    // Steals buckets starting at `pos`, replacing them with `bucket`.
    fn steal(&mut self, mut pos: usize, mut bucket: FullBucket<K, V>) {
        let mut my_dist = self.probe_distance(pos, self.which_bucket(bucket.2));

        while let Some(hash_code) = self.buckets[pos].as_ref().and_then(
            |bucket| if bucket.1.is_expired() {None} else {Some(bucket.2)}) {

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

                if !self.buckets[src].as_ref().unwrap().1.is_expired() {
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

impl<K, V> ModuloCapacity for WeakValueInnerMap<K, V> {
    fn capacity(&self) -> usize {
        self.buckets.len()
    }
}

impl<K, V, S> ModuloCapacity for WeakValueHashMap<K, V, S> {
    fn capacity(&self) -> usize {
        self.inner.capacity()
    }
}

impl<'a, K, V: WeakElement> ModuloCapacity for InnerEntry<'a, K, V> {
    fn capacity(&self) -> usize {
        self.map.capacity()
    }
}

impl<'a, K, V: WeakElement> ModuloCapacity for OccupiedEntry<'a, K, V> {
    fn capacity(&self) -> usize {
        self.inner.capacity()
    }
}

impl<'a, K, V: WeakElement> ModuloCapacity for VacantEntry<'a, K, V> {
    fn capacity(&self) -> usize {
        self.inner.capacity()
    }
}

impl<K, V> Debug for WeakValueInnerMap<K, V>
    where K: Debug,
          V: WeakElement,
          V::Strong: Debug
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{{ ")?;
        for (i, bucket) in self.buckets.iter().enumerate() {
            if let Some((k, v, _)) = bucket {
                write!(f, "[{}] {:?} => {:?}, ", i, *k, v.view())?;
            }
        }
        write!(f, "}}")
    }
}

impl<K: Debug, V: WeakElement, S> Debug for WeakValueHashMap<K, V, S>
    where V::Strong: Debug
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, K: Debug, V: WeakElement> Debug for Entry<'a, K, V>
    where V::Strong: Debug
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match *self {
            Entry::Occupied(ref e)  => e.fmt(f),
            Entry::Vacant(ref e)    => e.fmt(f),
        }
    }
}

impl<'a, K: Debug, V: WeakElement> Debug for OccupiedEntry<'a, K, V>
    where V::Strong: Debug
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, K: Debug, V: WeakElement> Debug for VacantEntry<'a, K, V>
    where V::Strong: Debug
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.inner.fmt(f)
    }
}

impl<'a, K: Debug, V: WeakElement> Debug for InnerEntry<'a, K, V>
    where V::Strong: Debug
{
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "InnerEntry {{ pos = {}, buckets = {:?} }}", self.pos, self.map)
    }
}

impl<K, V: WeakElement, S> IntoIterator for WeakValueHashMap<K, V, S> {
    type Item = (K, V::Strong);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            size: self.inner.len,
            base: self.inner.buckets.into_vec().into_iter(),
        }
    }
}

impl<'a, K, V: WeakElement, S> IntoIterator for &'a WeakValueHashMap<K, V, S> {
    type Item = (&'a K, V::Strong);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            base: self.inner.buckets.iter(),
            size: self.inner.len,
        }
    }
}

impl<K, V: WeakElement, S> WeakValueHashMap<K, V, S> {
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


