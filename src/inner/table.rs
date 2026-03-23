use crate::compat::*;

use hashbrown::hash_table as raw;
use hashbrown::HashTable as RawTable;

use crate::util::hash_one;

use super::{Element, Key, MaybeHash};

#[derive(Clone)]
pub(crate) struct Table<K, V, S> {
    // XXXX
    pub(crate) table: RawTable<(K, V)>,
    hash_builder: S,
}

pub(crate) struct OccupiedEntry<'a, K: Element + 'a, V: Element + 'a> {
    // XXXX
    pub(crate) inner: raw::OccupiedEntry<'a, (K, V)>,
    k_up: K::Upgraded,
    v_up: V::Upgraded,
}

pub(crate) struct VacantEntry<'a, K: Element + 'a, V: 'a> {
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
    pub(crate) fn remove_expired_inner(&mut self) {
        self.table
            .retain(|(k, v)| !(k.is_expired() || v.is_expired()));
    }

    pub(crate) fn remove_expired(&mut self) {
        self.remove_expired_inner();
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

        self.remove_expired_inner();
        let new_len = self.table.len();

        if new_len + additional < grow_at_threshold(orig_capacity) {
            return Ok(());
        }

        let n_to_grow = (orig_capacity - new_len) + 1;
        self.table
            .try_reserve(n_to_grow, Self::make_hasher(&self.hash_builder))?;
        assert!(self.table.capacity() > orig_capacity); // XXXX
        Ok(())
    }

    pub(crate) fn shrink_to_fit(&mut self) {
        // XXXX allow additional space?
        self.remove_expired_inner();
        self.table
            .shrink_to_fit(Self::make_hasher(&self.hash_builder));
    }

    pub(crate) fn entry(&mut self, key: K::Owned) -> Entry<'_, K, V> {
        let hash = K::hash_owned(&key, &self.hash_builder);
        self.try_reserve(1)
            .expect("Unable to allocate space for entry!");
        match self.table.entry(
            hash,
            |(k, _v)| k.eq_owned(&key),
            Self::make_hasher(&self.hash_builder),
        ) {
            raw::Entry::Occupied(mut occupied_entry) => {
                let (k, v) = occupied_entry.get_mut();
                if let Some(v_up) = v.upgrade() {
                    // Here is where we change the key, if appropriate.
                    // We don't need tto upgrade k, since we are going to
                    // replace it.
                    let k_up = K::upgraded_from_owned(&key);
                    k.reset_from_upgrade(&k_up);

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
        let hash = hash_one(&self.hash_builder, key);
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

    pub(crate) fn find<Q>(&self, key: &Q) -> Option<(K::Ref<'_>, V::Ref<'_>)>
    where
        Q: ?Sized + Hash + Eq,
        K::Key: Borrow<Q>,
    {
        let hash = hash_one(&self.hash_builder, key);
        let (k, v) = self.table.find(hash, |(k, _)| k.eq_borrow(key))?;
        if let (Some(k_ref), Some(v_ref)) = (k.as_ref(), v.as_ref()) {
            Some((k_ref, v_ref))
        } else {
            None
        }
    }

    /* XXXX
    pub(crate) fn retain<F>(&mut self, mut func: F)
    where
        F: FnMut(K::Ref<'_>, V::Ref<'_>) -> bool,
    {
        self.table.retain(|(k, v)| {
            if let (Some(k_ref), Some(v_ref)) = (k.as_ref(), v.as_ref()) {
                func(k_ref, v_ref)
            } else {
                false
            }
        })
    }
    */
}

impl<K: Element, V: Element, S> Table<K, V, S> {
    pub(crate) fn iter(&self) -> Iter<'_, K, V> {
        Iter {
            iter: self.table.iter(),
        }
    }

    pub(crate) fn into_iter(self) -> IntoIter<K, V> {
        IntoIter {
            iter: self.table.into_iter(),
        }
    }

    pub(crate) fn drain(&mut self) -> Drain<'_, K, V> {
        Drain {
            iter: self.table.drain(),
        }
    }
}

impl<K: Key, T, S: BuildHasher> Table<K, super::Owned<T>, S> {
    pub(crate) fn find_mut<Q>(&mut self, key: &Q) -> Option<(K::Ref<'_>, &mut T)>
    where
        Q: ?Sized + Hash + Eq,
        K::Key: Borrow<Q>,
    {
        let hash = hash_one(&self.hash_builder, key);
        let (k, v) = self.table.find_mut(hash, |(k, _)| k.eq_borrow(key))?;
        if let Some(k_ref) = k.as_ref() {
            Some((k_ref, &mut v.val))
        } else {
            None
        }
    }
}

impl<K: Element, T, S> Table<K, super::Owned<T>, S> {
    /* XXXX
    pub(crate) fn retain_mut<F>(&mut self, mut func: F)
    where
        F: FnMut(K::Ref<'_>, &mut T) -> bool,
    {
        self.table.retain(|(k, v)| {
            if let Some(k_ref) = k.as_ref() {
                func(k_ref, &mut v.val)
            } else {
                false
            }
        })
    }
    */

    pub(crate) fn iter_mut(&mut self) -> IterMut<'_, K, super::Owned<T>> {
        IterMut {
            iter: self.table.iter_mut(),
        }
    }
}

impl<'a, K: Element + 'a, V: Element + 'a> OccupiedEntry<'a, K, V> {
    pub(crate) fn get(&'a self) -> (&'a K::Owned, &'a V::Owned) {
        let (k, v) = self.inner.get();
        (
            K::owned_ref_from_upgrade(k, &self.k_up),
            V::owned_ref_from_upgrade(v, &self.v_up),
        )
    }
    pub(crate) fn remove(self) -> (K::Owned, V::Owned) {
        // TODO: It would be nice to expose vacant when possible.
        let ((k, v), _vacant) = self.inner.remove();
        (
            K::owned_from_upgrade(k, self.k_up),
            V::owned_from_upgrade(v, self.v_up),
        )
    }
}

impl<'a, K: Element + 'a, V: Element<CachedHash = ()> + 'a> OccupiedEntry<'a, K, V> {
    pub(crate) fn insert(&mut self, value: V::Owned) -> V::Owned {
        let (_k, v) = self.inner.get_mut();
        let (mut new_val, mut v_up) = V::from_owned(value, ());

        mem::swap(v, &mut new_val);
        mem::swap(&mut self.v_up, &mut v_up);

        V::owned_from_upgrade(new_val, v_up)
    }
}

impl<'a, K: Key + 'a, T: 'a> OccupiedEntry<'a, K, super::Owned<T>> {
    /* XXXX
    pub(crate) fn get_mut(&'a mut self) -> (&'a K::Owned, &'a mut T) {
        let (k, v) = self.inner.get_mut();
        (K::owned_ref_from_upgrade(k, &self.k_up), &mut v.val)
    }
    */

    pub(crate) fn into_mut(self) -> &'a mut T {
        &mut self.inner.into_mut().1.val
    }
}

impl<'a, K: Element + 'a, V: Element<CachedHash = ()> + 'a> VacantEntry<'a, K, V> {
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
}

impl<'a, K: Element + 'a, V: Element + 'a> VacantEntry<'a, K, V> {
    pub(crate) fn into_key(self) -> K::Owned {
        self.pending_key
    }

    pub(crate) fn key(&self) -> &K::Owned {
        &self.pending_key
    }
}

#[derive(Debug, Clone)]
pub(crate) struct Iter<'a, K, V> {
    iter: raw::Iter<'a, (K, V)>,
}

impl<'a, K: Element, V: Element> Iterator for Iter<'a, K, V> {
    type Item = (K::Ref<'a>, V::Ref<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        for (k, v) in &mut self.iter {
            if let (Some(k_ref), Some(v_ref)) = (k.as_ref(), v.as_ref()) {
                return Some((k_ref, v_ref));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[derive(Debug)]
pub(crate) struct IterMut<'a, K, V> {
    iter: raw::IterMut<'a, (K, V)>,
}

impl<'a, K: Element, T> Iterator for IterMut<'a, K, super::Owned<T>> {
    type Item = (K::Ref<'a>, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        for (k, super::Owned { val }) in &mut self.iter {
            if let Some(k_ref) = k.as_ref() {
                return Some((k_ref, val));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[derive(Debug)]
pub(crate) struct IntoIter<K, V> {
    iter: raw::IntoIter<(K, V)>,
}

impl<K: Element, V: Element> Iterator for IntoIter<K, V> {
    type Item = (K::Owned, V::Owned);

    fn next(&mut self) -> Option<Self::Item> {
        for (k, v) in &mut self.iter {
            if let (Some(k_owned), Some(v_owned)) = (k.into_owned(), v.into_owned()) {
                return Some((k_owned, v_owned));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[derive(Debug)]
pub(crate) struct Drain<'a, K, V> {
    iter: raw::Drain<'a, (K, V)>,
}

impl<'a, K: Element, V: Element> Iterator for Drain<'a, K, V> {
    type Item = (K::Owned, V::Owned);

    fn next(&mut self) -> Option<Self::Item> {
        for (k, v) in &mut self.iter {
            if let (Some(k_owned), Some(v_owned)) = (k.into_owned(), v.into_owned()) {
                return Some((k_owned, v_owned));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, K: Element + 'a, V: Element + 'a> fmt::Debug for OccupiedEntry<'a, K, V>
where
    K::Owned: fmt::Debug,
    V::Owned: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (k, v) = self.get();
        f.debug_struct("OccupiedEntry")
            .field("key", k)
            .field("val", v)
            .finish()
    }
}

impl<'a, K: Element + 'a, V: Element + 'a> fmt::Debug for VacantEntry<'a, K, V>
where
    K::Owned: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let k = self.key();
        f.debug_struct("VacantEntry").field("key", k).finish()
    }
}

fn grow_at_threshold(cap: usize) -> usize {
    div_ceil(cap, 4) * 3
}

fn div_ceil(a: usize, b: usize) -> usize {
    a.saturating_add(b - 1) / b
}
