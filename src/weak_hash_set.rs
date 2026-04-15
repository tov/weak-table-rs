//! A hash set where the elements are held by weak pointers and compared by value.

use crate::compat::*;
use crate::inner;
use crate::macros::*;

use super::traits::*;
use super::weak_key_hash_map as base;

pub use super::WeakHashSet;

universal_hashless_members! {
    WeakHashSet ("`WeakHashSet`", a "set")
    base::WeakKeyHashMap::with_capacity_and_hasher
    {T}
}

impl<T: WeakKey, S: BuildHasher> WeakHashSet<T, S> {
    /// Removes all expired elements.
    ///
    /// *O*(*n*) time
    pub fn remove_expired(&mut self) {
        self.0.remove_expired();
    }

    /// Reserves room for additional elements.
    ///
    /// This method ensures that at least `additional_capacity` insertions
    /// may be performed without reallocating.
    ///
    /// *O*(*n*) time
    pub fn reserve(&mut self, additional_capacity: usize) {
        self.0.reserve(additional_capacity);
    }

    /// Tries to reserve room for additional elements.
    ///
    /// If this method succeeds, then at least `additional_capacity` insertions
    /// may be performed without reallocating further.
    ///
    /// *O*(*n*) time
    pub fn try_reserve(
        &mut self,
        additional_capacity: usize,
    ) -> Result<(), crate::TryReserveError> {
        self.0.try_reserve(additional_capacity)
    }

    /// Shrinks the capacity to the minimum allowed to hold the current number of elements.
    ///
    /// *O*(*n*) time
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit();
    }

    /// Shrinks capacity to hold no fewer than `min_capacity` elements.
    ///
    /// May remove expired items if necessary.
    /// Does nothing if the current capacity is already at `min_capacity` or below.
    ///
    /// *O*(*n*) time
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.0.shrink_to(min_capacity);
    }

    // TODO: Non-ptr WeakHashSet should probably have `get` method.

    /// Returns true if the set contains the specified key.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        Q: ?Sized + Eq + Hash,
        T::Key: Borrow<Q>,
    {
        self.0.contains_key(key)
    }

    /// Gets a strong reference to the given key, if found.
    ///
    /// # Examples
    ///
    /// ```
    /// use weak_table::WeakHashSet;
    /// use std::rc::{Rc, Weak};
    /// use std::ops::Deref;
    ///
    /// let mut set: WeakHashSet<Weak<String>> = WeakHashSet::new();
    ///
    /// let a = Rc::new("a".to_owned());
    /// set.insert(a.clone());
    ///
    /// let also_a = set.get("a").unwrap();
    ///
    /// assert!(Rc::ptr_eq( &a, &also_a ));
    /// ```
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn get<Q>(&self, key: &Q) -> Option<T::Strong>
    where
        Q: ?Sized + Eq + Hash,
        T::Key: Borrow<Q>,
    {
        self.0.get_key(key)
    }

    /// Unconditionally inserts `key` into this set,
    /// replacing any previous matching entry.
    ///
    /// Returns true if the key was absent before, and false otherwise.
    ///
    /// (Note that unlike `HashSet::insert`, this insert method always replaces
    /// the key.)
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn insert(&mut self, key: T::Strong) -> bool {
        self.0.insert(key, ()).is_some()
    }

    /// Removes the entry matching the given key, if it exists.
    ///
    /// Returns true if an entry was removed.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn remove<Q>(&mut self, key: &Q) -> bool
    where
        Q: ?Sized + Eq + Hash,
        T::Key: Borrow<Q>,
    {
        self.0.remove(key).is_some()
    }

    /// Removes the entry matching the given key, if it exists, and return the it.
    ///
    /// expected *O*(1) time; worst-case *O*(*p*) time
    pub fn take<Q>(&mut self, key: &Q) -> Option<T::Strong>
    where
        Q: ?Sized + Eq + Hash,
        T::Key: Borrow<Q>,
    {
        self.0.remove_entry(key).map(|(k, ())| k)
    }

    /// Removes all elements not satisfying the given predicate.
    ///
    /// Also removes any expired elements.
    ///
    /// *O*(*n*) time
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(T::Strong) -> bool,
    {
        self.0.retain(|k, _| f(k));
    }

    /// Is self a subset of other?
    ///
    /// expected *O*(*n*) time; worst-case *O*(*nq*) time (where *n* is
    /// `self.capacity()` and *q* is the length of the probe sequences
    /// in `other`)
    pub fn is_subset<S1>(&self, other: &WeakHashSet<T, S1>) -> bool
    where
        S1: BuildHasher,
    {
        self.0.domain_is_subset(&other.0)
    }

    /// Helper: return true if 'self' contains 'item'.
    fn contains_strong(&self, item: &T::Strong) -> bool {
        T::with_key(item, |k| self.contains(k))
    }

    set_op_methods! {WeakHashSet}
    set_relationships! {WeakHashSet}
}

/// An iterator over the elements of a set.
pub struct Iter<'a, T: 'a>(base::Keys<'a, T, ()>);

impl<'a, T: WeakElement> Iterator for Iter<'a, T> {
    type Item = T::Strong;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

/// A consuming iterator over the elements of a set.
pub struct IntoIter<T>(base::IntoIter<T, ()>);

impl<T: WeakElement> Iterator for IntoIter<T> {
    type Item = T::Strong;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|pair| pair.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

/// A draining iterator over the elements of a set.
///
/// Once this iterator is dropped, all elements are removed from the set,
/// whether the iterator itself was drained or not.
pub struct Drain<'a, T: 'a>(base::Drain<'a, T, ()>);

impl<'a, T: WeakElement> Iterator for Drain<'a, T> {
    type Item = T::Strong;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|pair| pair.0)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<T: WeakElement, S> WeakHashSet<T, S> {
    /// Gets an iterator over the elements of this set.
    ///
    /// *O*(1) time
    pub fn iter(&self) -> Iter<'_, T> {
        Iter(self.0.keys())
    }

    /// Gets a draining iterator, which removes all the elements but retains the storage.
    ///
    /// *O*(1) time (and *O*(*n*) time to dispose of the result)
    pub fn drain(&mut self) -> Drain<'_, T> {
        Drain(self.0.drain())
    }

    /// Gets an iterator that removes and returns elements matching a given predicate.
    ///
    /// Expired elements are also removed.
    ///
    /// If this iterator is dropped before it is completed, then no further
    /// elements are removed.
    /// (This is in contrast to the behavior of [`drain`](Self::drain)).
    ///
    /// *O*(1) time
    pub fn extract_if<'a, F>(&'a mut self, mut f: F) -> ExtractIf<'a, T, F>
    where
        F: FnMut(T::Strong) -> bool + 'a,
    {
        ExtractIf {
            inner: self.0 .0.extract_if(move |e| {
                if let Some(k) = e.0.val.view() {
                    f(k)
                } else {
                    true
                }
            }),
            _phantom: PhantomData,
        }
    }
}

/// An iterator that removes members that match a given predicate.
pub struct ExtractIf<'a, T: WeakElement, F> {
    /// The underlying iterator.
    inner: inner::ExtractIf<'a, inner::WeakK<T>, inner::Owned<()>>,
    /// A marker so that F does not appear unused.
    _phantom: PhantomData<F>,
}

impl<'a, T: WeakElement, F> Iterator for ExtractIf<'a, T, F> {
    type Item = T::Strong;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, ())| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

set_op_types! {WeakHashSet where {T: WeakKey}}
set_operators! {WeakHashSet where {T: WeakKey}}

impl<T, S, S1> PartialEq<WeakHashSet<T, S1>> for WeakHashSet<T, S>
where
    T: WeakKey,
    S: BuildHasher,
    S1: BuildHasher,
{
    fn eq(&self, other: &WeakHashSet<T, S1>) -> bool {
        self.0 == other.0
    }
}

impl<T: WeakKey, S: BuildHasher> Eq for WeakHashSet<T, S> where T::Key: Eq {}

impl<T, S> FromIterator<T::Strong> for WeakHashSet<T, S>
where
    T: WeakKey,
    S: BuildHasher + Default,
{
    fn from_iter<I: IntoIterator<Item = T::Strong>>(iter: I) -> Self {
        WeakHashSet(base::WeakKeyHashMap::<T, (), S>::from_iter(
            iter.into_iter().map(|k| (k, ())),
        ))
    }
}

impl<T: WeakKey, const N: usize> From<[T::Strong; N]> for WeakHashSet<T, RandomState> {
    /// Converts an array of elements into a set.
    ///
    /// If any entries in the array are equal,
    /// all but one of the corresponding values will be dropped.
    fn from(value: [T::Strong; N]) -> Self {
        Self::from_iter(value)
    }
}

impl<T: WeakKey, S: BuildHasher> Extend<T::Strong> for WeakHashSet<T, S> {
    fn extend<I: IntoIterator<Item = T::Strong>>(&mut self, iter: I) {
        self.0.extend(iter.into_iter().map(|k| (k, ())));
    }
}

impl<T: WeakElement, S> Debug for WeakHashSet<T, S>
where
    T::Strong: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: WeakElement, S> IntoIterator for WeakHashSet<T, S> {
    type Item = T::Strong;
    type IntoIter = IntoIter<T>;

    /// Creates an owning iterator from `self`.
    ///
    /// *O*(1) time (and *O*(*n*) time to dispose of the result)
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self.0.into_iter())
    }
}

impl<'a, T: WeakElement, S> IntoIterator for &'a WeakHashSet<T, S> {
    type Item = T::Strong;
    type IntoIter = Iter<'a, T>;

    /// Creates a borrowing iterator from `self`.
    ///
    /// *O*(1) time
    fn into_iter(self) -> Self::IntoIter {
        Iter(self.0.keys())
    }
}

/// Helper: Given two references to sets, return them in ascending order of
/// len().
fn sort_by_size<'a, T: WeakKey, S: BuildHasher>(
    a: &'a WeakHashSet<T, S>,
    b: &'a WeakHashSet<T, S>,
) -> (&'a WeakHashSet<T, S>, &'a WeakHashSet<T, S>) {
    if a.len() < b.len() {
        (a, b)
    } else {
        (b, a)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::compat::rc::{Rc, Weak};

    crate::tests::common::empty_constructor_tests! {WeakHashSet<Weak<u8>>}
    crate::tests::set_operations::set_operation_tests! {WeakHashSet, 0}

    // Regression check for https://github.com/tov/weak-table-rs/issues/22
    #[test]
    fn test_retain_regresion() {
        // Run multiple iterations, since this was a heisenbug.
        for _ in 0..20 {
            let mut set: WeakHashSet<Weak<u8>> = WeakHashSet::default();
            let mut preserve_vals = Vec::new();

            const N: u8 = 50;

            for i in 0..N {
                let rc = Rc::new(i);
                preserve_vals.push(rc.clone());
                set.insert(rc);
            }

            let rc_n = Rc::new(N);
            set.insert(rc_n.clone());

            drop(preserve_vals);

            let mut retain_called_on = Vec::new();
            set.retain(|val| {
                retain_called_on.push(val);
                false
            });

            assert_eq!(retain_called_on, vec![rc_n]);
        }
    }

    #[test]
    fn test_take() {
        let s = [Rc::new(1), Rc::new(2), Rc::new(3)];
        let mut set: WeakHashSet<Weak<u32>> = s.clone().into();
        assert_eq!(set.iter().count(), 3);

        let v = set.take(&2);
        assert_eq!(v, Some(Rc::new(2)));
        assert_eq!(set.iter().count(), 2);
        assert!(Rc::ptr_eq(&v.expect("absent suddenly!"), &s[1]));

        let v = set.take(&2);
        assert!(v.is_none());
    }
}
