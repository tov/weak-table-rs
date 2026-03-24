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

        // XXXX Rethink these thresholds in light of the way that capacity can
        // shrink.
        if new_len + additional < grow_at_threshold(orig_capacity) {
            return Ok(());
        }

        let n_to_grow = (orig_capacity - new_len) + 1;
        self.table
            .try_reserve(n_to_grow, Self::make_hasher(&self.hash_builder))?;
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
                    // We don't need to upgrade k, since we are going to
                    // replace it.
                    // We don't need to check whether k is present, since
                    // eq_owned always returns false on a dangling reference.
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
        (0, self.iter.size_hint().1)
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
        (0, self.iter.size_hint().1)
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
        (0, self.iter.size_hint().1)
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
        (0, self.iter.size_hint().1)
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::compat::rc::{Rc, Weak};
    use crate::inner::{Owned, WeakK, WeakV};
    use crate::util::hash_one;

    // WeakKeyMap from u8 -> u8.
    type WkKeyMap = Table<WeakK<Weak<u8>>, Owned<u8>, RandomState>;
    // WeakWeakMap from u8 -> u8.
    type WkWkMap = Table<WeakK<Weak<u8>>, WeakV<Weak<u8>>, RandomState>;
    // WeakValMap
    type WkValMap = Table<Owned<u8>, WeakV<Weak<u8>>, RandomState>;

    impl<'a, K: Key + 'a, V: Element + 'a> super::Entry<'a, K, V> {
        fn unwrap_occupied(self) -> OccupiedEntry<'a, K, V> {
            match self {
                Entry::Occupied(e) => e,
                Entry::Vacant(_) => panic!("Entry was not occupied"),
            }
        }

        fn unwrap_vacant(self) -> VacantEntry<'a, K, V> {
            match self {
                Entry::Occupied(_) => panic!("Entry was not vacant"),
                Entry::Vacant(e) => e,
            }
        }
    }

    #[test]
    fn construct() {
        for cap in 0..64 {
            let tab = WkKeyMap::new(cap, RandomState::default());
            // XXXX: Document that capacity is a minimum.
            assert!(tab.capacity() >= cap);
        }
    }

    #[test]
    fn get_hasher() {
        let rs = RandomState::default();
        let tab = WkKeyMap::new(7, rs.clone());
        assert_eq!(hash_one(&rs, &13u8), hash_one(tab.hasher(), &13u8));
    }

    #[test]
    fn insert_len_clear() {
        // Insert entries, checking length and capacity.
        let mut tab = WkKeyMap::new(0, RandomState::default());
        let mut persist_keys = vec![];
        for n in 0..200 {
            let cap_orig = tab.capacity();
            let should_grow = tab.len() == tab.capacity();
            let k = Rc::new(n);
            tab.entry(k.clone()).unwrap_vacant().insert(n);
            persist_keys.push(k);

            assert_eq!(should_grow, tab.capacity() != cap_orig);

            assert_eq!(tab.len(), persist_keys.len());
            assert!(tab.capacity() >= tab.len());
        }

        // Clear the table; make sure that len changed but capacity didn't.
        let cap = tab.capacity();
        tab.clear();
        assert_eq!(tab.len(), 0);
        assert_eq!(tab.capacity(), cap);
    }

    #[test]
    fn insert_and_expire() {
        // Add entries that immediately expire; make sure we don't grow.
        let mut tab = WkKeyMap::new(7, RandomState::default());
        let cap_initial = tab.capacity();
        for n in 0..200 {
            let k = Rc::new(n);
            tab.entry(k.clone()).unwrap_vacant().insert(n);

            drop(k);
            // Nobody holds a strong reference, so this table's size should
            // never grow beyond the initial allocation.
        }
        assert_eq!(tab.capacity(), cap_initial);

        // Now insure that we _do_ grow when we are more than 3/4 full.
        let mut persist_keys = vec![];
        for n in 0..(cap_initial as u8 - 1) {
            let k = Rc::new(n);
            tab.entry(k.clone()).unwrap_vacant().insert(n);
            persist_keys.push(k);
        }
        for n in cap_initial as u8..200 {
            let k = Rc::new(n);
            tab.entry(k.clone()).unwrap_vacant().insert(n);
        }
        assert!(tab.capacity() > cap_initial);
        assert!(tab.capacity() < 150);
    }

    #[test]
    fn shrink_to_fit() {
        let mut tab = WkKeyMap::new(0, RandomState::default());
        let mut persist_keys = vec![];
        for n in 0..200 {
            let k = Rc::new(n);
            tab.entry(k.clone()).unwrap_vacant().insert(n);
            persist_keys.push(k);
        }
        let cap = tab.capacity();
        let buckets = tab.table.num_buckets();
        assert_eq!(tab.len(), 200);

        // This drops some of the strong references to the keys, but not all.
        persist_keys.truncate(17);
        assert_eq!(tab.len(), 200);
        assert_eq!(tab.capacity(), cap);

        // This removes expired keys.  The capacity will likely decrease,
        // since we have to leave "Deleted" placeholders in the table.
        //
        // The number of buckets will not decrease.
        tab.remove_expired_inner();
        assert_eq!(tab.len(), 17);
        assert!(tab.capacity() < cap);
        assert_eq!(tab.table.num_buckets(), buckets);

        // shrink_to_fit actually drops the space we don't need.
        tab.shrink_to_fit();
        assert!(tab.capacity() >= 17);
        assert!(tab.capacity() < cap);
        assert_eq!(tab.len(), 17);
        assert!(tab.table.num_buckets() < buckets);
    }

    #[test]
    fn entry_and_find() {
        let mut tab = WkKeyMap::new(0, RandomState::default());
        let u8_7 = Rc::new(7);
        let u8_9 = Rc::new(9);
        let u8_11 = Rc::new(11);

        tab.entry(u8_7.clone()).unwrap_vacant().insert(7);
        tab.entry(u8_9.clone()).unwrap_vacant().insert(9);
        tab.entry(u8_11.clone()).unwrap_vacant().insert(11);

        drop(u8_9);
        assert_eq!(tab.find(&7).unwrap(), (u8_7.clone(), &7));
        assert!(tab.find(&9).is_none());

        // Look up an occupied entry with a different key object: This should
        // change the key entry in the table.
        let u8_7_other = Rc::new(7);
        assert!(!Rc::ptr_eq(&u8_7, &u8_7_other));
        let e = tab.entry(u8_7_other.clone()).unwrap_occupied();
        assert_eq!(e.get().1, &7);
        assert_eq!(e.get().0, &u8_7_other);
        assert!(Rc::ptr_eq(&e.inner.get().0.upgrade().unwrap(), &u8_7_other));

        // Now use into_mut() to replace the value.
        //
        // We don't have a full get_mut, due to XXXXX lifetime issues.
        *e.into_mut() = 77;
        // This time use find_entry, which _shouldn't_ change the key in the table.
        let e = tab.find_entry(&7).unwrap();
        assert_eq!(e.get().1, &77);
        assert_eq!(e.get().0, &u8_7_other);
        assert_eq!(tab.find(&7).unwrap(), (u8_7, &77));

        // Now let's try an entry that is occupied in the underlying table,
        // but semantically vacant (because the value is unreferenced.)
        assert!(tab.find_entry(&9).is_none());
        let u8_9 = Rc::new(9);
        let e = tab.entry(u8_9.clone()).unwrap_vacant();
        let e = e.insert(99);
        assert_eq!(e.get().1, &99);
        assert!(Rc::ptr_eq(&e.inner.get().0.upgrade().unwrap(), &u8_9));
        let e = tab.find_entry(&9).unwrap();
        assert_eq!(e.get().1, &99);
        assert_eq!(tab.find(&9).unwrap(), (u8_9, &99));

        // Now try an entry that was vacant all along.
        let u8_13 = Rc::new(13);
        assert!(tab.find_entry(&13).is_none());
        let e = tab.entry(u8_13.clone()).unwrap_vacant();
        assert_eq!(e.key().as_ref(), &13);
        assert_eq!(e.into_key(), Rc::new(13));

        assert!(tab.find(&13).is_none());
    }

    #[test]
    fn entry_remove_replace() {
        let mut tab = WkKeyMap::new(0, RandomState::default());
        let u8_7 = Rc::new(7);
        let u8_9 = Rc::new(9);
        let u8_11 = Rc::new(11);

        tab.entry(u8_7.clone()).unwrap_vacant().insert(7);
        tab.entry(u8_9.clone()).unwrap_vacant().insert(9);
        tab.entry(u8_11.clone()).unwrap_vacant().insert(11);

        drop(u8_9);

        let mut e = tab.entry(u8_7.clone()).unwrap_occupied();
        let old = e.insert(77);
        assert_eq!(old, 7);
        assert_eq!(e.get().1, &77);

        let e = tab.entry(u8_11.clone()).unwrap_occupied();
        let old = e.remove();
        assert_eq!(&old.0, &u8_11);
        assert_eq!(old.1, 11);

        let v: Vec<_> = tab.into_iter().collect();
        assert_eq!(v, vec![(u8_7, 77)]);
    }

    #[test]
    fn find_mut() {
        let mut tab = WkKeyMap::new(0, RandomState::default());
        let u8_7 = Rc::new(7);
        let u8_9 = Rc::new(9);
        let u8_11 = Rc::new(11);

        tab.entry(u8_7.clone()).unwrap_vacant().insert(7);
        tab.entry(u8_9.clone()).unwrap_vacant().insert(9);
        tab.entry(u8_11.clone()).unwrap_vacant().insert(11);

        drop(u8_9);

        assert!(tab.find_mut(&9).is_none());
        assert!(tab.find_mut(&99).is_none());

        let (k, v) = tab.find_mut(&7).unwrap();
        assert_eq!(k, u8_7);
        assert_eq!(*v, 7);
        *v = 17;

        assert_eq!(tab.find(&7).unwrap().1, &17);
    }

    fn check_size_hint_ok(actual: usize, hint: (usize, Option<usize>)) {
        assert!(actual >= hint.0);
        if let Some(high) = hint.1 {
            assert!(actual <= high);
        }
    }

    #[test]
    fn iters_simple() {
        let mut tab = WkKeyMap::new(0, RandomState::default());
        let mut persist_keys = vec![];
        for n in 0..=15 {
            let k = Rc::new(n);
            tab.entry(k.clone()).unwrap_vacant().insert(n);
            if n & 1 == 1 {
                persist_keys.push(k);
            }
        }

        // Try iter_mut.
        let len = persist_keys.len();
        let itermut = tab.iter_mut();
        check_size_hint_ok(len, itermut.size_hint());

        let mut count = 0;
        for (k, v) in itermut {
            count += 1;
            assert!(persist_keys.contains(&k));
            *v *= *v;
        }
        assert_eq!(count, persist_keys.len());

        for k in persist_keys.iter() {
            assert_eq!(*tab.find(k).unwrap().1, k.as_ref() * k.as_ref());
        }

        // Try iter.
        let iter = tab.iter();
        check_size_hint_ok(len, iter.size_hint());
        let mut count = 0;
        for (k, v) in iter {
            count += 1;
            assert_eq!(*v, k.as_ref() * k.as_ref())
        }
        assert_eq!(count, persist_keys.len());

        // Try into_iter.
        let mut count = 0;
        let intoiter = tab.into_iter();
        check_size_hint_ok(len, intoiter.size_hint());
        for (k, v) in intoiter {
            count += 1;
            assert_eq!(v, k.as_ref() * k.as_ref())
        }
        assert_eq!(count, persist_keys.len());
    }

    #[test]
    fn drain() {
        let mut tab = WkKeyMap::new(0, RandomState::default());
        let mut persist_keys = vec![];
        for n in 0..100 {
            let k = Rc::new(n);
            tab.entry(k.clone()).unwrap_vacant().insert(n * 2);
            persist_keys.push(k);
        }
        let buckets = tab.table.num_buckets();
        assert_eq!(tab.len(), 100);

        // Check a few as we drrain them, then drop the Drain iterator.
        let drain = tab.drain();
        check_size_hint_ok(100, drain.size_hint());
        for (k, v) in drain.take(7) {
            assert_eq!(*k.as_ref() * 2, v);
        }

        assert_eq!(tab.len(), 0);
        // drain does not release storage.
        assert_eq!(tab.table.num_buckets(), buckets);
    }

    #[test]
    fn debug() {
        let mut tab = WkKeyMap::new(0, RandomState::default());
        let seventeen = Rc::new(17);
        let vacant = tab.entry(seventeen.clone()).unwrap_vacant();
        assert_eq!(format!("{:?}", &vacant), "VacantEntry { key: 17 }");
        let occupied = vacant.insert(23);
        assert_eq!(
            format!("{:?}", &occupied),
            "OccupiedEntry { key: 17, val: 23 }"
        );
    }

    #[test]
    fn weakweak_basics() {
        let mut tab = WkWkMap::new(0, RandomState::default());
        let mut persist_keys = vec![];
        let mut persist_vals = vec![];
        for n in 0..200 {
            let k = Rc::new(n);
            let v = Rc::new(n);
            tab.entry(k.clone()).unwrap_vacant().insert(v.clone());
            persist_keys.push(k);
            persist_vals.push(v);
        }

        assert_eq!(tab.len(), 200);

        persist_vals.reverse();
        persist_vals.truncate(190);
        persist_keys.truncate(190);

        assert_eq!(tab.len(), 200);
        assert_eq!(tab.iter().count(), 180);

        tab.remove_expired();

        assert_eq!(tab.len(), 180);
        assert_eq!(tab.iter().count(), 180);

        assert!(tab.find(&6).is_none());
        assert!(tab.find(&195).is_none());
        let p150 = tab.find(&150).unwrap();
        assert_eq!(p150.0.as_ref(), &150);
        assert_eq!(p150.1.as_ref(), &150);
    }

    #[test]
    fn weakweak_entry_cases() {
        let mut tab = WkWkMap::new(0, RandomState::default());
        let mut persist_keys = vec![];
        let mut persist_vals = vec![];
        for n in 0..200 {
            let k = Rc::new(n);
            let v = Rc::new(n);
            tab.entry(k.clone()).unwrap_vacant().insert(v.clone());
            persist_keys.push(k);
            persist_vals.push(v);
        }
        persist_vals.truncate(150);

        // Look up an entry for a key that never existed: it should be vacant.
        let k = Rc::new(220);
        let k2 = tab.entry(k.clone()).unwrap_vacant().into_key();
        assert!(Rc::ptr_eq(&k, &k2));

        // Look an entry for a key that exists: it should be present,
        // and looking it up should replace the key.
        let k_orig = persist_keys[100].clone();
        let k_new = Rc::new(100);
        assert_eq!(&k_new, &k_orig);
        assert!(!Rc::ptr_eq(&k, &k_orig));
        let e = tab.entry(k_new.clone()).unwrap_occupied();
        assert!(Rc::ptr_eq(e.get().0, &k_new));
        assert!(Rc::ptr_eq(e.get().1, &persist_vals[100]));

        // Look up an entry for a key exists but a value that is absent!
        // (This case can't occur for WeakKey maps.)
        let k = Rc::new(190);
        let e = tab.entry(k.clone()).unwrap_vacant();
        assert!(Rc::ptr_eq(e.key(), &k));
    }

    #[test]
    fn weakvalmap_basics() {
        let mut tab = WkValMap::new(0, RandomState::default());
        let mut persist_vals = vec![];
        for n in 0..100 {
            let v = Rc::new(n);
            tab.entry(n).unwrap_vacant().insert(v.clone());
            persist_vals.push(v);
        }

        assert_eq!(tab.find(&22).unwrap(), (&22, Rc::new(22)));
        assert_eq!(tab.entry(50).unwrap_occupied().remove(), (50, Rc::new(50)));
        persist_vals.truncate(50);
        assert_eq!(tab.iter().count(), 50);

        tab.remove_expired();
        assert_eq!(tab.len(), 50);
    }
}
