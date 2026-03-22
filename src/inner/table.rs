use std::borrow::Borrow;
use std::hash::{BuildHasher, Hash};

use hashbrown::hash_table as raw;
use hashbrown::HashTable as RawTable;

use super::{Element, Key, MaybeHash};

pub(crate) struct Table<K, V, S> {
    table: RawTable<(K, V)>,
    hash_builder: S,
}

pub(crate) struct OccupiedEntry<'a, K: Key + 'a, V: Element + 'a> {
    inner: raw::OccupiedEntry<'a, (K, V)>,
    k_up: K::Upgraded,
    v_up: V::Upgraded,
}

pub(crate) struct VacantEntry<'a, K: Key + 'a, V: 'a> {
    hash: K::CachedHash,
    inner: raw::VacantEntry<'a, (K, V)>,
    pending_key: K::Owned,
}

pub(crate) enum Entry<'a, K: Key + 'a, V: Element + 'a> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

impl<K, V, S> Table<K, V, S> {
    pub(crate) fn new(capacity: usize, hash_builder: S) -> Self {
        Self {
            table: RawTable::with_capacity(capacity),
            hash_builder,
        }
    }

    pub(crate) fn hasher(&self) -> &S {
        &self.hash_builder
    }

    pub(crate) fn capacity(&self) -> usize {
        self.table.capacity()
    }

    // Over-approximation.
    pub(crate) fn len(&self) -> usize {
        self.table.len()
    }

    pub(crate) fn clear(&mut self) {
        self.table.clear();
    }
}

impl<K: Key, V: Element, S> Table<K, V, S> {
    pub(crate) fn remove_expired(&mut self) {
        self.table
            .retain(|(k, v)| !(k.is_expired() || v.is_expired()));
    }
}

impl<K: Key, V: Element, S: BuildHasher> Table<K, V, S> {
    fn make_hasher(hash_builder: &S) -> impl Fn(&(K, V)) -> u64 + '_ {
        move |(k, _)| k.hash(hash_builder)
    }

    pub(crate) fn try_reserve(
        &mut self,
        additional: usize,
    ) -> Result<(), hashbrown::TryReserveError> {
        let orig_capacity = self.table.capacity();
        let orig_len = self.table.len();

        if orig_len + additional <= orig_capacity {
            return Ok(());
        }

        self.remove_expired();
        let new_len = self.table.len();

        // XXXX rounding.
        if new_len + additional <= (self.table.capacity() / 4) * 3 {
            return Ok(());
        }

        // XXXX round up, make sure cap is enough.
        self.table
            .try_reserve(new_len + additional, Self::make_hasher(&self.hash_builder))
    }

    pub(crate) fn entry(&mut self, key: K::Owned) -> Entry<'_, K, V> {
        // XXXX consider adjusting size!

        let hash = K::hash_owned(&key, &self.hash_builder);
        match self.table.entry(
            hash,
            |(k, _v)| k.eq_owned(&key),
            Self::make_hasher(&self.hash_builder),
        ) {
            raw::Entry::Occupied(occupied_entry) => {
                let (k, v) = occupied_entry.get();
                if let (Some(k_up), Some(v_up)) = (k.upgrade(), v.upgrade()) {
                    // XXXX weak_table replaces K in this case.!
                    Entry::Occupied(OccupiedEntry {
                        inner: occupied_entry,
                        k_up,
                        v_up,
                    })
                } else {
                    let (_, vacant_entry) = occupied_entry.remove();
                    Entry::Vacant(VacantEntry {
                        inner: vacant_entry,
                        pending_key: key,
                        hash: K::CachedHash::new(hash),
                    })
                }
            }
            raw::Entry::Vacant(vacant_entry) => Entry::Vacant(VacantEntry {
                inner: vacant_entry,
                pending_key: key,
                hash: K::CachedHash::new(hash),
            }),
        }
    }

    pub(crate) fn find_entry<Q>(&mut self, key: &Q) -> Option<OccupiedEntry<'_, K, V>>
    where
        Q: ?Sized + Hash + Eq,
        K::Key: Borrow<Q>,
    {
        let hash = self.hash_builder.hash_one(key);
        match self.table.find_entry(hash, |(k, _)| k.eq_borrow(key)) {
            Ok(occupied_entry) => {
                let (k, v) = occupied_entry.get();
                if let (Some(k_up), Some(v_up)) = (k.upgrade(), v.upgrade()) {
                    Some(OccupiedEntry {
                        inner: occupied_entry,
                        k_up,
                        v_up,
                    })
                } else {
                    None
                }
            }
            Err(_) => None,
        }
    }
}

impl<'a, K: Key + 'a, V: Element<CachedHash = ()> + 'a> VacantEntry<'a, K, V> {
    pub(crate) fn insert(self, val: V::Owned) -> OccupiedEntry<'a, K, V> {
        let (key, k_up) = K::from_owned(self.pending_key, self.hash);
        let (val, v_up) = V::from_owned(val, ());
        let occupied = self.inner.insert((key, val));
        OccupiedEntry {
            inner: occupied,
            k_up,
            v_up,
        }
    }

    pub(crate) fn into_key(self) -> K::Owned {
        self.pending_key
    }

    pub(crate) fn key(&self) -> &K::Owned {
        &self.pending_key
    }
}

pub(crate) struct Iter<'a, K, V> {
    iter: raw::Iter<'a, (K, V)>,
}

impl<'a, K: Key, V: Element> Iterator for Iter<'a, K, V> {
    type Item = (K::Ref<'a>, V::Ref<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        for (k, v) in &mut self.iter {
            if let (Some(k_ref), Some(v_ref)) = (k.as_ref(), v.as_ref()) {
                return Some((k_ref, v_ref));
            }
        }
        None
    }
}

pub(crate) struct IterMut<'a, K, V> {
    iter: raw::IterMut<'a, (K, V)>,
}

impl<'a, K: Key, T> Iterator for IterMut<'a, K, super::Owned<T>> {
    type Item = (K::Ref<'a>, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        for (k, super::Owned { val }) in &mut self.iter {
            if let Some(k_ref) = k.as_ref() {
                return Some((k_ref, val));
            }
        }
        None
    }
}

pub(crate) struct IntoIter<K, V> {
    iter: raw::IntoIter<(K, V)>,
}

impl<K: Key, V: Element> Iterator for IntoIter<K, V> {
    type Item = (K::Owned, V::Owned);

    fn next(&mut self) -> Option<Self::Item> {
        for (k, v) in &mut self.iter {
            if let (Some(k_owned), Some(v_owned)) = (k.into_owned(), v.into_owned()) {
                return Some((k_owned, v_owned));
            }
        }
        None
    }
}
