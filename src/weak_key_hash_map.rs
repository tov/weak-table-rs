use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash, Hasher};
use std::fmt::{self, Debug, Formatter};
use std::mem;

use super::traits::*;
use super::util::*;

const DEFAULT_INITIAL_CAPACITY: usize = 8;
const MAX_LOAD_FACTOR: f32 = 0.8;

type FullBucket<K, V> = (K, V, HashCode);
type Bucket<K, V> = Option<FullBucket<K, V>>;
type TablePtr<K, V> = Box<[Bucket<K, V>]>;

/// A mapping from weak pointers to values.
///
/// When a weak pointer expires, its mapping is lazily removed.
#[derive(Clone)]
pub struct WeakKeyHashMap<K, V, S = RandomState> {
    hash_builder: S,
    inner: MapInner<K, V>,
}

#[derive(Clone)]
struct MapInner<K, V> {
    buckets: TablePtr<K, V>,
    len: usize,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct HashCode(u64);

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
    map:        &'a mut MapInner<K, V>,
    pos:        usize,
    key:        K::Strong,
    hash_code:  HashCode,
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
            *option = None;
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
            hash_builder,
            inner: MapInner {
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
        let mut old_buckets = new_boxed_option_slice(capacity);
        mem::swap(&mut self.inner.buckets, &mut old_buckets);

        let iter = IntoIter {
            base: old_buckets.into_vec().into_iter(),
            size: self.inner.len,
        };

        for (key, value) in iter {
            self.entry_no_grow(key).or_insert(value);
        }
    }

    /// Removes all mappings whose keys have expired.
    pub fn remove_expired(&mut self) {
        self.retain(|_, _| true)
    }

    /// Returns an over-approximation of the number of elements.
    pub fn len(&self) -> usize {
        self.inner.len
    }

    /// Gets the requested entry.
    pub fn entry(&mut self, key: K::Strong) -> Entry<K, V> {
        // TODO: growing
        self.entry_no_grow(key)
    }

    pub fn entry_no_grow(&mut self, key: K::Strong) -> Entry<K, V> {
        let mut inner = {
            let hash_code = self.hash(K::view_key(&key));
            InnerEntry {
                pos:        self.which_bucket(hash_code),
                map:        &mut self.inner,
                hash_code,
                key,
            }
        };
        let mut dist = 0;

        loop {
            match inner.bucket_status() {
                BucketStatus::Unoccupied =>
                    return Entry::Vacant(VacantEntry(inner)),
                BucketStatus::MatchesKey =>
                    return Entry::Occupied(OccupiedEntry(inner)),
                BucketStatus::ProbeDistance(bucket_distance) => {
                    if bucket_distance > dist {
                        return Entry::Vacant(VacantEntry(inner))
                    } else {
                        inner.pos = inner.next_bucket(inner.pos);
                        dist += 1;
                    }
                }
            }
        }
    }

    /// Removes all associations from the map.
    pub fn clear(&mut self) {
        self.drain();
    }

    fn find_bucket<Q>(&self, key: &Q) -> Option<(usize, K::Strong, HashCode)>
        where Q: ?Sized + Hash + Eq,
              K::Key: Borrow<Q>
    {
        let hash_code = self.hash(key);
        let mut pos = self.which_bucket(hash_code);
        let mut dist = 0;

        loop {
            if let Some((ref weak_key, _, bucket_hash_code)) = self.inner.buckets[pos] {
                if bucket_hash_code == hash_code {
                    if let Some(bucket_key) = weak_key.view() {
                        if *K::view_key(&bucket_key).borrow() == *key {
                            return Some((pos, bucket_key, bucket_hash_code));
                        }
                    }
                }

                let bucket_dist =
                    self.probe_distance(pos, self.which_bucket(hash_code));
                if bucket_dist > dist {
                    return None;
                }
            } else {
                return None;
            }

            pos = self.next_bucket(pos);
            dist += 1;
        }
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

    /// Returns a mutable reference to the value corresponding to the key.
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
        where Q: ?Sized + Hash + Eq,
              K::Key: Borrow<Q>
    {
        self.find_bucket(key).and_then(move |tup|
            self.inner.buckets[tup.0].as_mut().map(|bucket| &mut bucket.1))
    }

    /// Unconditionally inserts the value, returning the old value if already present. Does not
    /// replace the key.
    pub fn insert(&mut self, key: K::Strong, value: V) -> Option<V> {
        match self.entry(key) {
            Entry::Occupied(mut occupied) => Some(occupied.insert(value)),
            Entry::Vacant(vacant) => {
                vacant.insert(value);
                None
            }
        }
    }

    /// Returns a mutable reference to the value corresponding to the key.
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

    fn hash<Q>(&self, key: &Q) -> HashCode
        where Q: ?Sized + Hash,
              K::Key: Borrow<Q>
    {
        let mut hasher = self.hash_builder.build_hasher();
        key.hash(&mut hasher);
        HashCode(hasher.finish())
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
        match self.map.buckets[self.pos] {
            Some((ref weak_key, _, hash_code)) => {
                if hash_code == self.hash_code {
                    if let Some(key) = weak_key.view() {
                        if K::view_key(&self.key) == K::view_key(&key) {
                            return BucketStatus::MatchesKey;
                        }
                    }
                }

                let dist = self.probe_distance(self.pos,
                                               self.which_bucket(hash_code));
                return BucketStatus::ProbeDistance(dist);
            },
            None => return BucketStatus::Unoccupied,
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
        mem::swap(self.get_mut(), &mut value);
        value
    }

    /// Removes the entry, returning the value.
    pub fn remove(self) -> V {
        self.remove_entry().1
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

impl<K: WeakKey, V> MapInner<K, V> {
    // Steals buckets starting at `pos`, replacing them with `bucket`.
    fn steal(&mut self, mut pos: usize, mut bucket: FullBucket<K, V>) {
        let mut dist = self.probe_distance(pos, self.which_bucket(bucket.2));

        loop {
            let hash_code_option =
                self.buckets[pos].as_ref().and_then(
                    |bucket| bucket.0.view().map(|_| bucket.2));

            if let Some(hash_code) = hash_code_option {
                let bucket_dist =
                    self.probe_distance(pos, self.which_bucket(hash_code));
                if dist > bucket_dist {
                    mem::swap(self.buckets[pos].as_mut().unwrap(), &mut bucket);
                    dist = bucket_dist;
                }
            } else {
                break;
            }

            pos = self.next_bucket(pos);
            dist += 1;
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

                if !self.buckets[src].as_ref().unwrap().0.expired() {
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

    fn which_bucket(&self, hash_code: HashCode) -> usize {
        hash_code.0 as usize % self.capacity()
    }
}

impl<K, V> ModuloCapacity for MapInner<K, V> {
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

fn debug_table<K: Debug, V: Debug>(buckets: &TablePtr<K, V>, f: &mut Formatter) -> fmt::Result {
    write!(f, "{{ ")?;
    for (i, bucket) in buckets.iter().enumerate() {
        if let &Some((ref k, ref v, hc)) = bucket {
            write!(f, "[{}] {:?} => {:?} ({:x}), ", i, *k, *v, hc.0)?;
        }
    }
    write!(f, "}}")
}

impl<K: Debug, V: Debug, S> Debug for WeakKeyHashMap<K, V, S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        debug_table(&self.inner.buckets, f)
    }
}

impl<'a, K: WeakKey + Debug, V: Debug> Debug for InnerEntry<'a, K, V> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "InnerEntry {{ pos = {}, buckets = ", self.pos)?;
        debug_table(&self.map.buckets, f)?;
        write!(f, " }}")
    }
}

impl<K: WeakKey, V, S> IntoIterator for WeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, V);
    type IntoIter = IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            size: self.inner.len,
            base: self.inner.buckets.into_vec().into_iter(),
        }
    }
}

impl<'a, K: WeakKey, V, S> IntoIterator for &'a WeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, &'a V);
    type IntoIter = Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            base: self.inner.buckets.iter(),
            size: self.inner.len,
        }
    }
}

impl<'a, K: WeakKey, V, S> IntoIterator for &'a mut WeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        IterMut {
            base: self.inner.buckets.iter_mut(),
            size: self.inner.len,
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
        let old_len = self.inner.len;
        self.inner.len = 0;
        Drain {
            base: self.inner.buckets.iter_mut(),
            size: old_len,
        }
    }
}
