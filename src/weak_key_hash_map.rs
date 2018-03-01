use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash, Hasher};
use std::fmt::{self, Debug, Formatter};
use std::mem;

use super::traits::*;
use super::util::*;

const DEFAULT_INITIAL_CAPACITY: usize = 8;

type Bucket<K, V> = Option<(K, V, u64)>;
type TablePtr<K, V> = Box<[Bucket<K, V>]>;

#[derive(Clone)]
pub struct WeakKeyHashMap<K, V, S = RandomState> {
    hash_builder: S,
    buckets: TablePtr<K, V>,
    len: usize,
}

#[derive(Debug)]
pub enum Entry<'a, K: 'a + WeakKey, V: 'a> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

#[derive(Debug)]
pub struct OccupiedEntry<'a, K: 'a + WeakKey, V: 'a>(InnerEntry<'a, K, V>);

#[derive(Debug)]
pub struct VacantEntry<'a, K: 'a + WeakKey, V: 'a>(InnerEntry<'a, K, V>);

struct InnerEntry<'a, K: 'a + WeakKey, V: 'a> {
    buckets: &'a mut TablePtr<K, V>,
    len: &'a mut usize,
    pos: usize,
    key: K::Strong,
    hash_code: u64,
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

    fn hash(&self, key: &K::Key) -> u64 {
        let mut hasher = self.hash_builder.build_hasher();
        key.hash(&mut hasher);
        hasher.finish()
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
