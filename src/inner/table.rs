use crate::compat::*;

use hashbrown::hash_table as raw;
use hashbrown::HashTable as RawTable;

use crate::util::hash_one;

use super::{Element, Key, MaybeHash};

/// An internal implementation type for all weak tables.
///
/// This type uses [`hashbrown::HashTable`] internally,
/// for performance and correctness.
///
/// Its key type is should be either a `Weak<T: WeakKey, u64>`,
/// or an `Owned<T>`.
///
/// Its value type  should be either a `Weak<T: WeakElement, ()>`,
/// or `Owned<T>`.
///
/// Since this is an internal type, we try to only implement the bare minimum
/// of functionality needed to implement the various weak tables.
#[derive(Clone)]
pub(crate) struct Table<K, V, S> {
    /// The underlying [`hashbrown::HashTable`].
    ///
    /// For correctness, all elements in this table must be inserted using
    /// hashes produced by running this object's `hash_builder`
    /// on their keys.
    ///
    // TODO: It would be nice if we did not have to make this pub(crate),
    // but we need it to implement retain().  See comment below beginning with
    // "TODO retain".
    pub(crate) table: RawTable<(K, V)>,

    /// The hash builder we use to hash elements in this table.
    hash_builder: S,
}

/// A mutable handle to an occupied entry in an internal [`Table`].
///
/// While this `OccupiedEntry` exists, the entry in the table cannot expire.
pub(crate) struct OccupiedEntry<'a, K: Element, V: Element> {
    /// The `OccupiedEntry` for the underlying [`hashbrown::HashTable`].
    ///
    // TODO: It would be nice if we did not have to make this pub(crate),
    // but we need it to implement get_mut().  See comment below beginning with
    // "TODO get_mut".
    pub(crate) inner: raw::OccupiedEntry<'a, (K, V)>,

    /// A handle used to prevent the key from disappearing (if it is weak)
    /// while this entrty exists.
    k_handle: K::Handle,

    /// A handle used to prevent the value from disappearing (if it is weak)
    /// While this entry exists.
    v_handle: V::Handle,
}

/// A mutable handle to a vacant entry in an internal [`Table`].
pub(crate) struct VacantEntry<'a, K: Element, V> {
    /// The `VacantEntry` for the underlying [`hashbrown::HashTable`].
    inner: raw::VacantEntry<'a, (K, V)>,

    /// The key that we will insert into the entry, if we are told to insert.
    pending_key: K::Owned,

    /// The hash of `pending_key`, if K is Weak.
    ///
    /// We need a hash in order to construct a [`Weak`](super::Weak) key,
    /// so we need to store either the hash itself, or a reference to the
    /// BuildHasher.
    /// We're going with the hash here, since we've already computed it,
    /// and we'd like to avoid excessive parameterization.
    pending_key_hash: K::CachedHash,
}

/// An internal enum for an entry in a [`Table`] that may be occupied or vacant.
///
/// Since this type is internal, we don't actually need to implement any methods
/// on it.
pub(crate) enum Entry<'a, K: Key, V: Element> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

impl<K, V, S> Table<K, V, S> {
    /// Construct a new `Table` with a given minimum `capacity`, and a given [`BuildHasher`].
    ///
    /// See notes on [`capacity`](Self::capacity).
    pub(crate) fn new(capacity: usize, hash_builder: S) -> Self {
        Self {
            table: RawTable::with_capacity(capacity),
            hash_builder,
        }
    }

    /// Return a reference to this table's [`BuildHasher`].
    pub(crate) fn hasher(&self) -> &S {
        &self.hash_builder
    }

    /// Return the current capacity of the table.
    ///
    /// We define the capacity an upper bound to the number of entries that
    /// this table can hold without reallocating.
    ///
    /// This calculation can behave surprisingly since [`hashbrown`] uses "Deleted"
    /// records internally in order to implement their
    /// [open-addressing hash table](https://en.wikipedia.org/wiki/Open_addressing).
    /// This makes deletion faster, but means that sometimes the table needs to
    /// be rebuilt _even if it does not have to grow_.
    /// Additionally, it means that `remove()` may reduce the capacity of the table.
    pub(crate) fn capacity(&self) -> usize {
        self.table.capacity()
    }

    /// Return an over-approximation of the number of entries in the table.
    ///
    /// This can be an over-approximation since it includes expired entries
    /// that have not yet been removed.
    pub(crate) fn len(&self) -> usize {
        self.table.len()
    }

    /// Remove all entries from this table.
    ///
    /// Does not reallocate.
    pub(crate) fn clear(&mut self) {
        self.table.clear();
    }
}

impl<K: Key, V: Element, S> Table<K, V, S> {
    /// Remove all expired entries from this table.
    ///
    /// This is an internal helper and does not reallocate.
    pub(crate) fn remove_expired_inner(&mut self) {
        self.table
            .retain(|(k, v)| !(k.is_expired() || v.is_expired()));
    }

    /// Remove all expired entries from this table.
    ///
    /// (At some point in the future, this may shrink the allocation, as the
    /// original `weak_table` implementation did.)
    pub(crate) fn remove_expired(&mut self) {
        self.remove_expired_inner();
    }
}

impl<K: Key, V: Element, S: BuildHasher> Table<K, V, S> {
    /// Construct a function from a `hash_builder` suitable for hashing the
    /// entries of this table.
    ///
    /// Many [`hashbrown::HashTable`] APIs need callbacks of this type.
    ///
    /// This can't take &self, for lifetime reasons.
    fn make_hasher(hash_builder: &S) -> impl Fn(&(K, V)) -> u64 + '_ {
        move |(k, _)| k.hash(hash_builder)
    }

    /// Ensure that this table has capacity to insert `additional` entries
    /// without reallocating.
    ///
    /// See caveats on [`Self::capacity`].
    pub(crate) fn try_reserve(
        &mut self,
        additional: usize,
    ) -> Result<(), hashbrown::TryReserveError> {
        let orig_capacity = self.table.capacity();
        let orig_len = self.table.len();

        // Check whether our existing capacity can handle this insertion.
        if orig_len + additional <= orig_capacity {
            return Ok(());
        }

        // TODO: Split the rest of this into a #[cold] function.

        // Remove all expired entries, and see whether doing so gave us enough
        // capacity to accommodate the request.  Make sure that in this case we
        // leave extra space so that we do not need to garbage-collect too often.
        self.remove_expired_inner();
        let new_len = self.table.len();

        // XXXX Rethink these thresholds in light of the way that capacity can
        // shrink.
        if new_len + additional < grow_at_threshold(orig_capacity) {
            return Ok(());
        }

        // We need to reallocate.

        // XXXX Rethink n_to_grow in light of the way that capacity can shrink.
        let n_to_grow = (orig_capacity - new_len) + 1;
        self.table
            .try_reserve(n_to_grow, Self::make_hasher(&self.hash_builder))?;
        Ok(())
    }

    /// Remove expired entries from this table, and reallocate it if appropriate
    /// to reduce its size.
    pub(crate) fn shrink_to_fit(&mut self) {
        self.remove_expired_inner();
        // TODO: Should we allow some additional space, as `weak-table` did?
        // It seems to violate the contract of `shrink_to_fit` though.
        self.table
            .shrink_to_fit(Self::make_hasher(&self.hash_builder));
    }

    /// Return an [`Entry`] corresponding to the occupied or unoccupied slot
    /// of the provided `key`.
    ///
    /// If K is a Weak key, we always replace any existing occupied entry's key with K.
    pub(crate) fn entry(&mut self, key: K::Owned) -> Entry<'_, K, V> {
        let hash = K::hash_owned(&key, &self.hash_builder);

        // Make sure that there is space for one more entry.
        //
        // We call this even though `hashbrown::HashTable::entry` will also
        // allocate as needed, since we may want to expire old entries, and we
        // may want to reallocate to a size other than `hashbrown` would choose.
        self.try_reserve(1)
            .expect("Unable to allocate space for entry!");

        match self.table.entry(
            hash,
            |(k, _v)| k.eq_owned(&key),
            Self::make_hasher(&self.hash_builder),
        ) {
            raw::Entry::Occupied(mut occupied_entry) => {
                let (k, v) = occupied_entry.get_mut();
                if let Some(v_handle) = v.handle() {
                    // We have found an existing occupied entry with a
                    // non-expired key and value.  (We know that the key was
                    // non-expired when we looked it up, since eq_owned
                    // succeeded.  If the entry's key expired between then and now,
                    // it doesn't matter, since we are about to replace it with `key`.

                    // Change the key if appropriate
                    let k_handle = K::handle_from_owned(&key);
                    k.reset_from_handle(&k_handle);

                    // Return the entry.
                    Entry::Occupied(OccupiedEntry {
                        inner: occupied_entry,
                        k_handle,
                        v_handle,
                    })
                } else {
                    // We found an entry with the desired key, but the value was expired.
                    //
                    // Remove the entry and transform it into a vacant entry.
                    let ((_k, _v), vacant_entry) = occupied_entry.remove();
                    Entry::Vacant(VacantEntry {
                        inner: vacant_entry,
                        pending_key: key,
                        pending_key_hash: K::CachedHash::new(hash),
                    })
                }
            }
            raw::Entry::Vacant(vacant_entry) => {
                // We found no existing entry.  Wrap the VacantEntry that we received.
                Entry::Vacant(VacantEntry {
                    inner: vacant_entry,
                    pending_key: key,
                    pending_key_hash: K::CachedHash::new(hash),
                })
            }
        }
    }

    /// Look up an `OccupiedEntry` for a given key, if there is one and it has not expired.
    ///
    /// Unlike `find_entry`, this method never has to reallocate the table, and
    /// never has to return a VacantEntry.
    ///
    /// It *does not* replace weak keys.
    pub(crate) fn find_entry<Q>(&mut self, key: &Q) -> Option<OccupiedEntry<'_, K, V>>
    where
        Q: ?Sized + Hash + Eq,
        K::Key: Borrow<Q>,
    {
        let hash = hash_one(&self.hash_builder, key);
        match self.table.find_entry(hash, |(k, _)| k.eq_borrow(key)) {
            Ok(occupied_entry) => {
                let (k, v) = occupied_entry.get();
                if let (Some(k_handle), Some(v_handle)) = (k.handle(), v.handle()) {
                    Some(OccupiedEntry {
                        inner: occupied_entry,
                        k_handle,
                        v_handle,
                    })
                } else {
                    // Key or value has expired.
                    None
                }
            }
            Err(_absent_entry) => {
                // No entry present.
                None
            }
        }
    }

    /// Look up the key and value for a given non-expired entry, if there is one.
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

    /* TODO retain:

    This implementation doesn't work, for lifetime and invariance reasons.

    It would be nice if we could fix it,
    so we could make our `table` field stop being pub(crate),
    and so we wouldn't have to have to maintain separate `retain()` implementations.

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
    /// Return an iterator over the non-expired entries in this Table, in an arbitrary order.
    pub(crate) fn iter(&self) -> Iter<'_, K, V> {
        Iter(self.table.iter())
    }

    /// Return a consuming iterator over the non-expired entries in this Table, in an arbitrary order.
    pub(crate) fn into_iter(self) -> IntoIter<K, V> {
        IntoIter(self.table.into_iter())
    }

    /// Return a draining iterator over the non-expired entries in this Table, in an arbitrary order.
    ///
    /// After this iterator is dropped, the table will be empty.  No
    /// reallocation is performed.
    pub(crate) fn drain(&mut self) -> Drain<'_, K, V> {
        Drain(self.table.drain())
    }
}

impl<K: Key, T, S: BuildHasher> Table<K, super::Owned<T>, S> {
    /// Return a reference to the key, and a mutable reference to the value, of
    /// an entry in the table.
    ///
    /// Only implemented for owned values.
    ///
    /// Returns None if an entry exists but it is expired.
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
    /*
      See "TODO retain" note above.

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

    /// Return an iterator over keys and mutable references to values in the table.
    ///
    /// Only implemented for owned values.
    pub(crate) fn iter_mut(&mut self) -> IterMut<'_, K, super::Owned<T>> {
        IterMut(self.table.iter_mut())
    }
}

impl<'a, K: Element, V: Element> OccupiedEntry<'a, K, V> {
    /// Return references to the key and value of this entry.
    pub(crate) fn get(&'a self) -> (&'a K::Owned, &'a V::Owned) {
        let (k, v) = self.inner.get();
        (
            K::owned_ref_from_handle(k, &self.k_handle),
            V::owned_ref_from_handle(v, &self.v_handle),
        )
    }

    /// Remove this entry and return its members.
    pub(crate) fn remove(self) -> (K::Owned, V::Owned) {
        // TODO: It would be nice to expose `_vacant` when possible.
        let ((k, v), _vacant) = self.inner.remove();
        (
            K::owned_from_handle(k, self.k_handle),
            V::owned_from_handle(v, self.v_handle),
        )
    }
}

impl<'a, K: Element, V: Element<CachedHash = ()>> OccupiedEntry<'a, K, V> {
    /// Replace the value of this `OccupiedEntry` with `value`.
    ///
    /// Return the previous value.
    pub(crate) fn insert(&mut self, value: V::Owned) -> V::Owned {
        // This is a little tricky because we need to replace self.inner.get_mut().1
        // _and_ self.v_handle.  Then we need to return an owned value
        // constructed from the previous values of those fields.

        let (_k, v) = self.inner.get_mut();
        let (mut new_val, mut v_handle) = V::from_owned(value, ());

        mem::swap(v, &mut new_val);
        mem::swap(&mut self.v_handle, &mut v_handle);

        V::owned_from_handle(new_val, v_handle)
    }
}

impl<'a, K: Key, T> OccupiedEntry<'a, K, super::Owned<T>> {
    /* TODO get_mut:

       Because of lifetime issues, this implementation isn't viable.
       It would be nice to fix this, so we can make OccupiedEntry completely opaque.

    pub(crate) fn get_mut(&'a mut self) -> (&'a K::Owned, &'a mut T) {
        let (k, v) = self.inner.get_mut();
        (K::owned_ref_from_handle(k, &self.k_handle), &mut v.val)
    }
    */

    /// Consume this `OccupiedEntry` returning a mutable pointer to its value.
    ///
    /// Only implemented for Owned values.
    pub(crate) fn into_mut(self) -> &'a mut T {
        &mut self.inner.into_mut().1.val
    }
}

impl<'a, K: Element, V: Element<CachedHash = ()>> VacantEntry<'a, K, V> {
    /// Insert `val` into this vacant entry, and return the resulting `OccupiedEntry`.
    pub(crate) fn insert(self, val: V::Owned) -> OccupiedEntry<'a, K, V> {
        let (key, k_handle) = K::from_owned(self.pending_key, self.pending_key_hash);
        let (val, v_handle) = V::from_owned(val, ());
        let occupied = self.inner.insert((key, val));
        OccupiedEntry {
            inner: occupied,
            k_handle,
            v_handle,
        }
    }
}

impl<'a, K: Element, V: Element> VacantEntry<'a, K, V> {
    /// Consume this `VacantEntry` and return the key that was used to
    /// construct it.
    pub(crate) fn into_key(self) -> K::Owned {
        self.pending_key
    }

    /// Return a reference to the key that was used to construct this `VacantEntry`.
    pub(crate) fn key(&self) -> &K::Owned {
        &self.pending_key
    }
}

/// An iterator over the keys and values in a [`Table`].
#[derive(Debug, Clone)]
pub(crate) struct Iter<'a, K, V>(raw::Iter<'a, (K, V)>);

impl<'a, K: Element, V: Element> Iterator for Iter<'a, K, V> {
    type Item = (K::Ref<'a>, V::Ref<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        for (k, v) in &mut self.0 {
            if let (Some(k_ref), Some(v_ref)) = (k.as_ref(), v.as_ref()) {
                return Some((k_ref, v_ref));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // We have to replace the lower bound with 0 since we don't know the
        // true lower bound: entries in the table may expire while we are
        // iterating over it.
        (0, self.0.size_hint().1)
    }
}

/// An iterator over the keys and mutable references to values in a [`Table`]
/// with Owned values.
#[derive(Debug)]
pub(crate) struct IterMut<'a, K, V>(raw::IterMut<'a, (K, V)>);

impl<'a, K: Element, T> Iterator for IterMut<'a, K, super::Owned<T>> {
    type Item = (K::Ref<'a>, &'a mut T);

    fn next(&mut self) -> Option<Self::Item> {
        for (k, super::Owned { val }) in &mut self.0 {
            if let Some(k_ref) = k.as_ref() {
                return Some((k_ref, val));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // We have to replace the lower bound with 0 since we don't know the
        // true lower bound: entries in the table may expire while we are
        // iterating over it.
        (0, self.0.size_hint().1)
    }
}

/// A consuming iterator over the keys and values in a [`Table`].
#[derive(Debug)]
pub(crate) struct IntoIter<K, V>(raw::IntoIter<(K, V)>);

impl<K: Element, V: Element> Iterator for IntoIter<K, V> {
    type Item = (K::Owned, V::Owned);

    fn next(&mut self) -> Option<Self::Item> {
        for (k, v) in &mut self.0 {
            if let (Some(k_owned), Some(v_owned)) = (k.into_owned(), v.into_owned()) {
                return Some((k_owned, v_owned));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // We have to replace the lower bound with 0 since we don't know the
        // true lower bound: entries in the table may expire while we are
        // iterating over it.
        (0, self.0.size_hint().1)
    }
}

/// A draining iterator over the keys and values in a [`Table`].
//
// Note: We don't need to implement Drop for this, since
// `hashbrown::hash_table::Drain` already implements Drop.
#[derive(Debug)]
pub(crate) struct Drain<'a, K, V>(raw::Drain<'a, (K, V)>);

impl<'a, K: Element, V: Element> Iterator for Drain<'a, K, V> {
    type Item = (K::Owned, V::Owned);

    fn next(&mut self) -> Option<Self::Item> {
        for (k, v) in &mut self.0 {
            if let (Some(k_owned), Some(v_owned)) = (k.into_owned(), v.into_owned()) {
                return Some((k_owned, v_owned));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // We have to replace the lower bound with 0 since we don't know the
        // true lower bound: entries in the table may expire while we are
        // iterating over it.
        (0, self.0.size_hint().1)
    }
}

impl<'a, K: Element, V: Element> fmt::Debug for OccupiedEntry<'a, K, V>
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

impl<'a, K: Element, V: Element> fmt::Debug for VacantEntry<'a, K, V>
where
    K::Owned: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let k = self.key();
        f.debug_struct("VacantEntry").field("key", k).finish()
    }
}

/// At what length threshold should a table of capacity `cap` grow?
///
/// We check this threshold only when we have removed expired entries from a table,
/// to see whether we should use the newly freed space, or whether we should
/// expand in order to avoid repeated garbage-collection steps.
fn grow_at_threshold(cap: usize) -> usize {
    div_ceil(cap, 4) * 3
}

/// Return CEIL(a / b).
///
/// We have to provide this because `usize::div_ceil` isn't available at our MSRV.
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

    impl<'a, K: Key, V: Element> super::Entry<'a, K, V> {
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
        assert!(Rc::ptr_eq(&e.inner.get().0.handle().unwrap(), &u8_7_other));

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
        assert!(Rc::ptr_eq(&e.inner.get().0.handle().unwrap(), &u8_9));
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
