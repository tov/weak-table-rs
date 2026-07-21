//! A hash map where the keys and values are both held by weak pointers, and keys are compared by
//! pointer.

use crate::common::*;
use crate::compat::*;

use super::by_ptr::*;
use super::traits::*;
use super::weak_weak_hash_map as base;

pub use super::weak_weak_hash_map::{
    Drain, Entry, ExtractIf, IntoIter, IntoKeys, IntoValues, Iter, Keys, Values,
};
pub use super::PtrWeakWeakHashMap;

universal_hashless_members! {
    PtrWeakWeakHashMap
    ("`PtrWeakWeakHashMap", a "map")
    crate::WeakWeakHashMap::with_capacity_and_hasher
    {K, V}
}

impl<K: WeakElement, V: WeakElement, S: BuildHasher> PtrWeakWeakHashMap<K, V, S>
where
    K::Strong: Deref,
{
    universal_key_independent_members! {"mappings"}

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
    pub fn get(&self, key: &K::Strong) -> Option<V::Strong> {
        self.0.get(&(key.deref() as *const _))
    }

    /// Returns true if the map contains the specified key.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn contains_key(&self, key: &K::Strong) -> bool {
        self.0.contains_key(&(key.deref() as *const _))
    }

    /// Unconditionally inserts the value, returning the old value if already present. Does not
    /// replace the key.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn insert(&mut self, key: K::Strong, value: V::Strong) -> Option<V::Strong> {
        self.0.insert(key, value)
    }

    /// Removes the entry with the given key, if it exists, and returns the value.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn remove(&mut self, key: &K::Strong) -> Option<V::Strong> {
        self.0.remove(&(key.deref() as *const _))
    }

    /// Removes all mappings not satisfying the given predicate.
    ///
    /// Also removes any expired mappings.
    ///
    /// *O*(*n*) time
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(K::Strong, V::Strong) -> bool,
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
        other: &PtrWeakWeakHashMap<K, V1, S1>,
        value_equal: F,
    ) -> bool
    where
        F: FnMut(V::Strong, V1::Strong) -> bool,
        V1: WeakElement,
        S1: BuildHasher,
    {
        self.0.is_submap_with(&other.0, value_equal)
    }

    /// Is self a submap of other?
    ///
    /// expected *O*(*n*) time; worst-case *O*(*nq*) time (where *n* is
    /// `self.capacity()` and *q* is the length of the probe sequences
    /// in `other`)
    pub fn is_submap<V1, S1>(&self, other: &PtrWeakWeakHashMap<K, V1, S1>) -> bool
    where
        V1: WeakElement,
        V::Strong: PartialEq<V1::Strong>,
        S1: BuildHasher,
    {
        self.0.is_submap(&other.0)
    }

    /// Are the keys of self a subset of the keys of other?
    ///
    /// expected *O*(*n*) time; worst-case *O*(*nq*) time (where *n* is
    /// `self.capacity()` and *q* is the length of the probe sequences
    /// in `other`)
    pub fn domain_is_subset<V1, S1>(&self, other: &PtrWeakWeakHashMap<K, V1, S1>) -> bool
    where
        V1: WeakElement,
        S1: BuildHasher,
    {
        self.0.domain_is_subset(&other.0)
    }
}

impl<K: WeakElement, V: WeakElement, S> PtrWeakWeakHashMap<K, V, S>
where
    K::Strong: Deref,
{
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
        F: FnMut(K::Strong, V::Strong) -> bool + 'a,
    {
        self.0.extract_if(f)
    }
}

impl<K, V, V1, S, S1> PartialEq<PtrWeakWeakHashMap<K, V1, S1>> for PtrWeakWeakHashMap<K, V, S>
where
    K: WeakElement,
    K::Strong: Deref,
    V: WeakElement,
    V1: WeakElement,
    V::Strong: PartialEq<V1::Strong>,
    S: BuildHasher,
    S1: BuildHasher,
{
    fn eq(&self, other: &PtrWeakWeakHashMap<K, V1, S1>) -> bool {
        self.0 == other.0
    }
}

impl<K: WeakElement, V: WeakElement, S: BuildHasher> Eq for PtrWeakWeakHashMap<K, V, S>
where
    K::Strong: Deref,
    V::Strong: Eq,
{
}

impl<K, V, S> FromIterator<(K::Strong, V::Strong)> for PtrWeakWeakHashMap<K, V, S>
where
    K: WeakElement,
    K::Strong: Deref,
    V: WeakElement,
    S: BuildHasher + Default,
{
    fn from_iter<T: IntoIterator<Item = (K::Strong, V::Strong)>>(iter: T) -> Self {
        PtrWeakWeakHashMap(base::WeakWeakHashMap::<ByPtr<K>, V, S>::from_iter(iter))
    }
}

#[cfg(any(test, feature = "std", feature = "ahash"))]
impl<K, V, const N: usize> From<[(K::Strong, V::Strong); N]>
    for PtrWeakWeakHashMap<K, V, RandomState>
where
    K: WeakElement,
    K::Strong: Deref,
    V: WeakElement,
{
    /// Converts an array of key-value pairs into a map.
    ///
    /// If any entries in the array have equal keys,
    /// all but one of the corresponding values will be dropped.
    fn from(value: [(K::Strong, V::Strong); N]) -> Self {
        Self::from_iter(value)
    }
}

impl<K, V, S> Extend<(K::Strong, V::Strong)> for PtrWeakWeakHashMap<K, V, S>
where
    K: WeakElement,
    K::Strong: Deref,
    V: WeakElement,
    S: BuildHasher,
{
    fn extend<T: IntoIterator<Item = (K::Strong, V::Strong)>>(&mut self, iter: T) {
        self.0.extend(iter);
    }
}

impl<K, V, S> Debug for PtrWeakWeakHashMap<K, V, S>
where
    K: WeakElement,
    K::Strong: Debug,
    V: WeakElement,
    V::Strong: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<K: WeakElement, V: WeakElement, S> IntoIterator for PtrWeakWeakHashMap<K, V, S> {
    type Item = (K::Strong, V::Strong);
    type IntoIter = IntoIter<ByPtr<K>, V>;

    /// Creates an owning iterator from `self`.
    ///
    /// *O*(1) time (and *O*(*n*) time to dispose of the result)
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, K: WeakElement, V: WeakElement, S> IntoIterator for &'a PtrWeakWeakHashMap<K, V, S> {
    type Item = (K::Strong, V::Strong);
    type IntoIter = Iter<'a, ByPtr<K>, V>;

    /// Creates a borrowing iterator from `self`.
    ///
    /// *O*(1) time
    fn into_iter(self) -> Self::IntoIter {
        (&self.0).into_iter()
    }
}

#[cfg(test)]
mod test {
    #![allow(clippy::print_stderr)]
    // TODO 050: remove.
    #![cfg_attr(feature = "ahash", allow(deprecated))]

    use super::{Entry, PtrWeakWeakHashMap};
    use crate::{
        compat::{
            eprintln, format,
            rc::{Rc, Weak},
            Vec,
        },
        tests::util::VecDebugAsMap,
    };

    crate::tests::common::empty_constructor_tests! {PtrWeakWeakHashMap<Weak<u32>, Weak<u32>>}

    //    fn show_me(weakmap: &PtrWeakWeakHashMap<Weak<u32>, Weak<f32>>) {
    //        for (key, _) in weakmap {
    //            eprint!(" {:2}", *key);
    //        }
    //        eprintln!();
    //    }

    // From https://github.com/tov/weak-table-rs/issues/1#issuecomment-461858060
    #[test]
    fn insert_and_check() {
        let mut rcs: Vec<(Rc<u32>, Rc<f32>)> = Vec::new();

        for i in 0..200 {
            rcs.push((Rc::new(i), Rc::new(i as f32 + 0.1)));
        }

        let mut weakmap: PtrWeakWeakHashMap<Weak<u32>, Weak<f32>> = PtrWeakWeakHashMap::new();

        for (key, value) in rcs.iter().cloned() {
            weakmap.insert(key, value);
            //            show_me(&weakmap);
        }

        let mut count = 0;

        for (key, value) in &rcs {
            assert!(weakmap.contains_key(key));

            match weakmap.entry(Rc::clone(key)) {
                Entry::Occupied(occ) => {
                    assert_eq!(occ.get(), value);
                    count += 1;
                }
                Entry::Vacant(_) => {
                    eprintln!("PointerWeakWeakHashMap: missing: {}", *key);
                }
            }
        }

        assert_eq!(count, rcs.len());
    }

    #[test]
    fn debug_map() {
        let rcs: Vec<Rc<u32>> = (0..20).map(Rc::new).collect();
        let map: PtrWeakWeakHashMap<Weak<u32>, Weak<u32>> =
            rcs.iter().map(|n| (n.clone(), n.clone())).collect();
        let vec: VecDebugAsMap<_, _> = map.iter().collect();
        assert_eq!(format!("{map:?}"), format!("{vec:?}"));
    }

    #[test]
    fn is_submap() {
        let mut zero_rcs: Vec<Rc<u32>> = (0..50).map(|_| Rc::new(0)).collect();
        let rcs: Vec<Rc<u32>> = (0..50).map(Rc::new).collect();

        let weakmap: PtrWeakWeakHashMap<Weak<u32>, Weak<u32>> = zero_rcs
            .iter()
            .zip(rcs.iter())
            .take(25)
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        let mut weakmap2 = weakmap.clone();

        assert!(weakmap.is_submap(&weakmap2));
        assert!(weakmap2.is_submap(&weakmap));

        weakmap2.extend(
            zero_rcs
                .iter()
                .zip(rcs.iter())
                .skip(25)
                .map(|(k, v)| (k.clone(), v.clone())),
        );
        assert!(weakmap.is_submap(&weakmap2));
        assert!(!weakmap2.is_submap(&weakmap));
        assert!(weakmap.domain_is_subset(&weakmap2));
        assert!(!weakmap2.domain_is_subset(&weakmap));

        weakmap2.insert(zero_rcs[0].clone(), rcs[12].clone());
        assert!(!weakmap.is_submap(&weakmap2));
        assert!(!weakmap2.is_submap(&weakmap));
        assert!(weakmap.submap_with(&weakmap2, |_v1, _v2| true));
        assert!(!weakmap2.submap_with(&weakmap, |_v1, _v2| true));

        let _ = zero_rcs.remove(0);
        assert!(weakmap.is_submap(&weakmap2));
    }
}
