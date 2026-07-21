//! A hash map where the keys are held by weak pointers and compared by pointer.

use crate::common::*;
use crate::compat::*;

use super::by_ptr::*;
use super::traits::*;
use super::weak_key_hash_map as base;

pub use super::weak_key_hash_map::{
    Drain, Entry, ExtractIf, IntoIter, IntoKeys, IntoValues, Iter, IterMut, Keys, Values, ValuesMut,
};
pub use super::PtrWeakKeyHashMap;

universal_hashless_members! {
    PtrWeakKeyHashMap
    ("`PtrWeakKeyHashMap", a "map")
    crate::WeakKeyHashMap::with_capacity_and_hasher
    {K, V}
}

impl<K: WeakElement, V, S: BuildHasher> PtrWeakKeyHashMap<K, V, S>
where
    K::Strong: Deref,
{
    universal_key_independent_members! {"mappings"}

    /// The proportion of buckets that
    /// Gets the requested entry.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn entry(&mut self, key: K::Strong) -> Entry<'_, ByPtr<K>, V> {
        self.0.entry(key)
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// Returns `None` if no matching key is found.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn get(&self, key: &K::Strong) -> Option<&V> {
        self.0.get(&(key.deref() as *const _))
    }

    /// Returns true if the map contains the specified key.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn contains_key(&self, key: &K::Strong) -> bool {
        self.0.contains_key(&(key.deref() as *const _))
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// Returns `None` if no matching key is found.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn get_mut(&mut self, key: &K::Strong) -> Option<&mut V> {
        let p = key.deref() as *const _;
        self.0.get_mut(&p)
    }

    /// Looks up mutable references to the values corresponding to several keys
    /// at a time.
    ///
    /// (Because of borrowing rules, Rust doesn't allow you to call `get_mut()` again
    /// while the result of a previous `get_mut()` is still live.  This method exists
    /// to work around that limitation.)
    ///
    /// Only one mutable reference can exist to any given value at a time.
    /// Therefore, all keys must refer to different values, or this
    /// method will panic.
    ///
    /// expected *O*(1 `N^2`) time; worst-case *O*(*p* `N^2`) time,
    /// where N is the length of the array.
    ///
    /// # Panics
    ///
    /// Panics if any keys refer to the same value.
    pub fn get_disjoint_mut<const N: usize>(&mut self, ks: [&K::Strong; N]) -> [Option<&mut V>; N] {
        let ks: [*const <K::Strong as Deref>::Target; N] = ks.map(|k| (*k).deref() as *const _);
        let ks_refs = crate::util::each_ref(&ks);

        self.0
             .0
            .get_disjoint_mut(ks_refs)
            .map(|ent| ent.map(|(_k, v)| v))
    }

    /// Unconditionally inserts the value, returning the old value if already present. Does not
    /// replace the key.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn insert(&mut self, key: K::Strong, value: V) -> Option<V> {
        self.0.insert(key, value)
    }

    /// Removes the entry with the given key, if it exists, and returns the value.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn remove(&mut self, key: &K::Strong) -> Option<V> {
        self.0.remove(&(key.deref() as *const _))
    }

    /// Removes all mappings not satisfying the given predicate.
    ///
    /// Also removes any expired mappings.
    ///
    /// *O*(*n*) time
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(K::Strong, &mut V) -> bool,
    {
        self.0.retain(f);
    }

    /// Is this map a submap of the other, using the given value comparison.
    ///
    /// In particular, all the keys of self must be in other and the values must compare true with
    /// value_equal.
    ///
    /// expected *O*(*n*) time; worst-case *O*(*nq*) time (where *n* is
    /// `self.capacity()` and *q* is the length of the probe sequences
    /// in `other`)
    pub fn submap_with<F, S1, V1>(
        &self,
        other: &PtrWeakKeyHashMap<K, V1, S1>,
        value_equal: F,
    ) -> bool
    where
        F: FnMut(&V, &V1) -> bool,
        S1: BuildHasher,
    {
        self.0.is_submap_with(&other.0, value_equal)
    }

    /// Is self a submap of other?
    ///
    /// expected *O*(*n*) time; worst-case *O*(*nq*) time (where *n* is
    /// `self.capacity()` and *q* is the length of the probe sequences
    /// in `other`)
    pub fn is_submap<V1, S1>(&self, other: &PtrWeakKeyHashMap<K, V1, S1>) -> bool
    where
        V: PartialEq<V1>,
        S1: BuildHasher,
    {
        self.0.is_submap(&other.0)
    }

    /// Are the keys of self a subset of the keys of other?
    ///
    /// expected *O*(*n*) time; worst-case *O*(*nq*) time (where *n* is
    /// `self.capacity()` and *q* is the length of the probe sequences
    /// in `other`)
    pub fn domain_is_subset<V1, S1>(&self, other: &PtrWeakKeyHashMap<K, V1, S1>) -> bool
    where
        S1: BuildHasher,
    {
        self.0.domain_is_subset(&other.0)
    }
}

impl<K: WeakElement, V, S> PtrWeakKeyHashMap<K, V, S> {
    /// Gets an iterator over the keys and values.
    ///
    /// *O*(1) time
    pub fn iter(&self) -> Iter<'_, ByPtr<K>, V> {
        self.0.iter()
    }

    /// Gets an iterator over the keys.
    ///
    /// *O*(1) time
    pub fn keys(&self) -> Keys<'_, ByPtr<K>, V> {
        self.0.keys()
    }

    /// Gets an iterator over the values.
    ///
    /// *O*(1) time
    pub fn values(&self) -> Values<'_, ByPtr<K>, V> {
        self.0.values()
    }

    /// Gets an iterator over the keys and mutable values.
    ///
    /// *O*(1) time
    pub fn iter_mut(&mut self) -> IterMut<'_, ByPtr<K>, V> {
        self.0.iter_mut()
    }

    /// Gets an iterator over the mutable values.
    ///
    /// *O*(1) time
    pub fn values_mut(&mut self) -> ValuesMut<'_, ByPtr<K>, V> {
        self.0.values_mut()
    }

    /// Gets a draining iterator, which removes all the values but retains the storage.
    ///
    /// *O*(1) time (and *O*(*n*) time to dispose of the result)
    pub fn drain(&mut self) -> Drain<'_, ByPtr<K>, V> {
        self.0.drain()
    }

    ptr_into_kv_methods! {}

    /// Gets an iterator that removes and returns elements matching a given predicate.
    ///
    /// Expired elements are also removed.
    ///
    /// If this iterator is dropped before it is completed, then no further
    /// elements are removed.
    /// (This is in contrast to the behavior of [`drain`](Self::drain)).
    ///
    /// *O*(1) time
    pub fn extract_if<'a, F>(&'a mut self, f: F) -> ExtractIf<'a, ByPtr<K>, V, F>
    where
        F: FnMut(K::Strong, &mut V) -> bool + 'a,
    {
        self.0.extract_if(f)
    }
}

impl<K, V, V1, S, S1> PartialEq<PtrWeakKeyHashMap<K, V1, S1>> for PtrWeakKeyHashMap<K, V, S>
where
    K: WeakElement,
    K::Strong: Deref,
    V: PartialEq<V1>,
    S: BuildHasher,
    S1: BuildHasher,
{
    fn eq(&self, other: &PtrWeakKeyHashMap<K, V1, S1>) -> bool {
        self.0 == other.0
    }
}

impl<K: WeakElement, V: Eq, S: BuildHasher> Eq for PtrWeakKeyHashMap<K, V, S> where K::Strong: Deref {}

impl<'a, K, V, S> Index<&'a K::Strong> for PtrWeakKeyHashMap<K, V, S>
where
    K: WeakElement,
    K::Strong: Deref,
    S: BuildHasher,
{
    type Output = V;

    fn index(&self, index: &'a K::Strong) -> &Self::Output {
        self.0.index(&(index.deref() as *const _))
    }
}

impl<'a, K, V, S> IndexMut<&'a K::Strong> for PtrWeakKeyHashMap<K, V, S>
where
    K: WeakElement,
    K::Strong: Deref,
    S: BuildHasher,
{
    fn index_mut(&mut self, index: &'a K::Strong) -> &mut Self::Output {
        self.0.index_mut(&(index.deref() as *const _))
    }
}

impl<K, V, S> FromIterator<(K::Strong, V)> for PtrWeakKeyHashMap<K, V, S>
where
    K: WeakElement,
    K::Strong: Deref,
    S: BuildHasher + Default,
{
    fn from_iter<T: IntoIterator<Item = (K::Strong, V)>>(iter: T) -> Self {
        PtrWeakKeyHashMap(base::WeakKeyHashMap::<ByPtr<K>, V, S>::from_iter(iter))
    }
}

#[cfg(any(test, feature = "std", feature = "ahash"))]
impl<K, V, const N: usize> From<[(K::Strong, V); N]> for PtrWeakKeyHashMap<K, V, RandomState>
where
    K: WeakElement,
    K::Strong: Deref,
{
    /// Converts an array of key-value pairs into a map.
    ///
    /// If any entries in the array have equal keys,
    /// all but one of the corresponding values will be dropped.
    fn from(value: [(K::Strong, V); N]) -> Self {
        Self::from_iter(value)
    }
}

impl<K, V, S> Extend<(K::Strong, V)> for PtrWeakKeyHashMap<K, V, S>
where
    K: WeakElement,
    K::Strong: Deref,
    S: BuildHasher,
{
    fn extend<T: IntoIterator<Item = (K::Strong, V)>>(&mut self, iter: T) {
        self.0.extend(iter);
    }
}

impl<'a, K, V, S> Extend<(&'a K::Strong, &'a V)> for PtrWeakKeyHashMap<K, V, S>
where
    K: 'a + WeakElement,
    K::Strong: Clone + Deref,
    V: 'a + Clone,
    S: BuildHasher,
{
    fn extend<T: IntoIterator<Item = (&'a K::Strong, &'a V)>>(&mut self, iter: T) {
        self.0.extend(iter);
    }
}

impl<K, V: Debug, S> Debug for PtrWeakKeyHashMap<K, V, S>
where
    K: WeakElement,
    K::Strong: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<K: WeakElement, V, S> IntoIterator for PtrWeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, V);
    type IntoIter = IntoIter<ByPtr<K>, V>;

    /// Creates an owning iterator from `self`.
    ///
    /// *O*(1) time (and *O*(*n*) time to dispose of the result)
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, K: WeakElement, V, S> IntoIterator for &'a PtrWeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, &'a V);
    type IntoIter = Iter<'a, ByPtr<K>, V>;

    /// Creates a borrowing iterator from `self`.
    ///
    /// *O*(1) time
    fn into_iter(self) -> Self::IntoIter {
        (&self.0).into_iter()
    }
}

impl<'a, K: WeakElement, V, S> IntoIterator for &'a mut PtrWeakKeyHashMap<K, V, S> {
    type Item = (K::Strong, &'a mut V);
    type IntoIter = IterMut<'a, ByPtr<K>, V>;

    /// Creates a borrowing iterator from `self`.
    ///
    /// *O*(1) time
    fn into_iter(self) -> Self::IntoIter {
        (&mut self.0).into_iter()
    }
}

#[cfg(test)]
mod test {
    #![allow(clippy::print_stderr)]

    use super::{Entry, PtrWeakKeyHashMap};
    use crate::{
        compat::{
            eprintln, format,
            rc::{Rc, Weak},
            Vec,
        },
        tests::util::VecDebugAsMap,
    };

    crate::tests::common::empty_constructor_tests! {PtrWeakKeyHashMap<Weak<u32>, u32>}

    //    fn show_me(weakmap: &PtrWeakKeyHashMap<Weak<u32>, f32>) {
    //        for (key, _) in weakmap {
    //            eprint!(" {:2}", *key);
    //        }
    //        eprintln!();
    //    }

    // From https://github.com/tov/weak-table-rs/issues/1#issuecomment-461858060
    #[test]
    fn insert_and_check() {
        let mut rcs: Vec<Rc<u32>> = Vec::new();

        for i in 0..200 {
            rcs.push(Rc::new(i));
        }

        let mut weakmap: PtrWeakKeyHashMap<Weak<u32>, f32> = PtrWeakKeyHashMap::new();

        for item in rcs.iter().cloned() {
            let f = *item as f32 + 0.1;
            weakmap.insert(item, f);
        }

        let mut count = 0;

        for item in &rcs {
            assert!(weakmap.contains_key(item));

            match weakmap.entry(Rc::clone(item)) {
                Entry::Occupied(_) => count += 1,
                Entry::Vacant(_) => eprintln!("PointerWeakKeyHashMap: missing: {}", *item),
            }
        }

        assert_eq!(count, rcs.len());
    }

    #[test]
    fn debug_map() {
        let rcs: Vec<Rc<u32>> = (0..20).map(Rc::new).collect();
        let map: PtrWeakKeyHashMap<Weak<u32>, u32> =
            rcs.iter().map(|n| (n.clone(), **n * 7)).collect();
        let vec: VecDebugAsMap<_, _> = map.iter().collect();
        assert_eq!(format!("{map:?}"), format!("{vec:?}"));
    }

    #[test]
    fn is_submap() {
        let mut rcs: Vec<Rc<u32>> = (0..50).map(|_| Rc::new(0)).collect();
        let weakmap: PtrWeakKeyHashMap<Weak<u32>, u32> =
            rcs.iter().take(25).map(|n| (n.clone(), **n)).collect();
        let mut weakmap2 = weakmap.clone();

        assert!(weakmap.is_submap(&weakmap2));
        assert!(weakmap2.is_submap(&weakmap));

        weakmap2.extend(rcs.iter().skip(25).map(|n| (n.clone(), **n)));
        assert!(weakmap.is_submap(&weakmap2));
        assert!(!weakmap2.is_submap(&weakmap));
        assert!(weakmap.domain_is_subset(&weakmap2));
        assert!(!weakmap2.domain_is_subset(&weakmap));

        weakmap2.insert(rcs[0].clone(), 12);
        assert!(!weakmap.is_submap(&weakmap2));
        assert!(!weakmap2.is_submap(&weakmap));
        assert!(weakmap.submap_with(&weakmap2, |_v1, _v2| true));
        assert!(!weakmap2.submap_with(&weakmap, |_v1, _v2| true));

        let _ = rcs.remove(0);
        assert!(weakmap.is_submap(&weakmap2));
    }
}
