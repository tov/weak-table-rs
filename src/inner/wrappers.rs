//! Wrappers around Weak and Owned types, used to implement our internal [`Table`].
//!
//! [`Table`]: super::Table

use crate::compat::*;

use crate::{
    traits::{WeakElement, WeakKey},
    util::hash_one,
};

/// A type that can be Owned or Weak.
///
/// Since this needs to be implemented by our [`Owned`] wrapper,
/// we cannot use [`WeakElement`] for this.
pub(crate) trait Element: Sized {
    /// The owned type corresponding to this type.
    ///
    /// | Element type | Self               | Owned                  |
    /// | ------------ | ------------------ | ---------------------- |
    /// | Weak         | `Weak<WeakPtr<T>>` | `StrongPtr<T>`         |
    /// | Owned        | `Owned<T>`         | `T`                    |
    type Owned;

    /// A reference to this type, that our APIs return.
    ///
    /// | Element type | Self               |  Ref                   |
    /// | ------------ | ------------------ | ---------------------- |
    /// | Weak         | `Weak<WeakPtr<T>>` | `StrongPtr<T>`         |
    /// | Owned        | `Owned<T>`         | `&T`                   |
    type Ref<'a>
    where
        Self: 'a;

    /// A value that we must hold in order to prevent this element from "disappearing".
    ///
    /// We hold this in our [`Entry`](super::Entry) types
    /// so that weak pointers do not expire while an `Entry` is live.
    ///
    /// | Element type | Self               |  Handle                |
    /// | ------------ | ------------------ | ---------------------- |
    /// | Weak         | `Weak<WeakPtr<T>>` | `StrongPtr<T>`         |
    /// | Owned        | `Owned<T>`         | `()`                   |
    type Handle;

    /// A value that we need to store in order to be able to recover the hash of
    /// this element.
    ///
    /// We need to store hashes for weak elements because
    /// if they disappear, we can no longer compute their hashes,
    /// but `hashbrown` requires that keys never change their hashes.
    ///
    /// | Element type | Self                    |  CachedHash       |
    /// | ------------ | ----------------------- | ----------------- |
    /// | Weak key     | `Weak<WeakPtr<T>, u64>` | `u64`             |
    /// | Weak value   | `Weak<WeakPtr<T>, ()>`  | `()`              |
    /// | Owned        | `Owned<T>`              | `()`              |
    type CachedHash: MaybeHash;

    /// Try to return a [`Ref`](Self::Ref) for this value.
    ///
    /// Return None if this is an expired weak pointer.
    ///
    /// | Element type | Input              | Output                             |
    /// | ------------ | ------------------ | ---------------------------------- |
    /// | Weak         | `&Weak<WeakPtr<T>>`| `Option<StrongPtr<T>>`             |
    /// | Owned        | `&Owned<T>`,       | `Some(&T)`                         |
    fn as_ref(&self) -> Option<Self::Ref<'_>>;

    /// Return true if this is an expired weak pointer.
    fn is_expired(&self) -> bool;

    /// Return any value that we need to hold in order to keep this element from
    /// disappearing.
    ///
    /// | Element type | Input               | Output                 |
    /// | ------------ | ------------------- | ---------------------- |
    /// | Weak         | `&Weak<WeakPtr<T>>` | `Option<StrongPtr<T>>` |
    /// | Owned        | `&Owned<T>`         | `Some(())`             |
    fn handle(&self) -> Option<Self::Handle>;

    /// Create a new instance of this element from its Owned form and a hash value.
    ///
    /// Return this element, and a [`Self::Handle`]` to hold
    /// in order to prevent this this element from disappearing.
    ///
    /// | Element type | Input             | Output                             |
    /// | ------------ | ----------------- | ---------------------------------- |
    /// | Weak         | `Strong<T>`, `u64`| `(Weak<WeakPtr<T>>, StrongPtr<T>)` |
    /// | Owned        | `T`, `u64`        | `(T, ())`                          |
    fn from_owned(owned: Self::Owned, cached_hash: Self::CachedHash) -> (Self, Self::Handle);

    /// Try to convert this element into its owned form.
    ///
    /// | Element type | Input              | Output                             |
    /// | ------------ | ------------------ | ---------------------------------- |
    /// | Weak         | `Weak<WeakPtr<T>>` | `Option<StrongPtr<T>>`             |
    /// | Owned        | `Owned<T>`,        | `Some(T))`                         |
    fn into_owned(self) -> Option<Self::Owned>;

    /// Convert a reference this element,
    /// plus a reference to a [`Self::Handle`],
    /// into a reference to the Owned form of this element.
    ///
    /// | Element type | Input                                | Output          |
    /// | ------------ | ------------------------------------ | --------------- |
    /// | Weak         | `&Weak<WeakPtr<T>>`, `&StrongPtr<T>` | `&StrongPtr<T>` |
    /// | Owned        | `&Owned<T>`, `&()`                   | `&T`            |
    fn owned_ref_from_handle<'a>(&'a self, handle: &'a Self::Handle) -> &'a Self::Owned;

    /// Convert an owned instance of this element,
    /// plus an owned instance of a [`Self::Handle`],
    /// into an Owned instance of this element.
    ///
    /// | Element type | Input                              | Output         |
    /// | ------------ | ---------------------------------- | -------------- |
    /// | Weak         | `Weak<WeakPtr<T>>`, `StrongPtr<T>` | `StrongPtr<T>` |
    /// | Owned        | `Owned<T>`, `()`                   | `T`            |
    fn owned_from_handle(self, handle: Self::Handle) -> Self::Owned;

    /// Given a reference to an owned copy of the element,
    /// return a [`Self::Handle`] that we have to hold
    /// to keep the owned copy from disappearing if it is downgraded
    /// to a weak pointer.
    ///
    /// | Element type | Input           | Output         |
    /// | ------------ | --------------- | -------------- |
    /// | Weak         | `&StrongPtr<T>` | `StrongPtr<T>` |
    /// | Owned        | `&T`            | `()`           |
    fn handle_from_owned(owned: &Self::Owned) -> Self::Handle;

    /// If this element is weak,
    /// change it to live as long as the provided [`Self::Handle`].
    ///
    /// Requirements: Only use this when `handle` == `self`.
    ///
    /// We use this to implement the behavior of [`Table::entry()`](super::Table::entry)
    /// for weak keys.
    ///
    /// | Element type | Input                                    | Behavior |
    /// | ------------ | ---------------------------------------- | -------- |
    /// | Weak         | `&mut Weak<WeakPtr<T>>`, `&StrongPtr<T>` | `self = handle.downgrade()` |
    /// | Owned        | `&mut Owned<T>`, `&T`                    | {}       |
    fn reset_from_handle(&mut self, handle: &Self::Handle);
}

/// A type that can be Owned or Weak, and which can be used as key.
///
/// Since this needs to be implemented by our [`Owned`] wrapper,
/// we cannot use [`WeakKey`] for this.
pub(crate) trait Key: Element + Sized {
    /// The underlying key type that
    type Key: ?Sized;

    /// Compute a hash of this element using a provided hash-builder.
    ///
    /// (For weak elements, the hash needs to be pre-computed and stored.)
    fn hash<S: BuildHasher>(&self, hash_builder: &S) -> u64;

    /// Compute a hash of an owned instance of this element.
    fn hash_owned<S: BuildHasher>(strong: &Self::Owned, hash_builder: &S) -> u64;

    /// Return true if this element is not expired, and it is equal to a given
    /// owned value.
    ///
    /// Always return false for expired Weak pointers.
    fn eq_owned(&self, strong: &Self::Owned) -> bool;

    /// Return true if this element is semantically equivalent to key that it
    /// can be borrowed as.
    ///
    /// Always return false for expired Weak pointers.
    fn eq_borrow<Q>(&self, key: &Q) -> bool
    where
        Q: ?Sized + Hash + Eq,
        Self::Key: Borrow<Q>;
}

/// An owned element in a [`Table`](super::Table).
///
/// This is used internally to hold the keys in a [`WeakValueHashMap`](crate::WeakValueHashMap),
/// or the values in a [`WeakKeyHashMap`](crate::WeakKeyHashMap).
#[derive(Clone, Debug)]
pub(crate) struct Owned<T> {
    /// The actual owned value.
    pub(crate) val: T,
}

impl<T> Element for Owned<T> {
    type Owned = T;
    type Ref<'a>
        = &'a T
    where
        T: 'a;
    type Handle = ();
    type CachedHash = ();

    fn is_expired(&self) -> bool {
        false
    }

    fn as_ref(&self) -> Option<Self::Ref<'_>> {
        Some(&self.val)
    }
    fn handle(&self) -> Option<Self::Handle> {
        Some(())
    }

    fn from_owned(val: Self::Owned, _hash: ()) -> (Self, Self::Handle) {
        (Owned { val }, ())
    }

    fn into_owned(self) -> Option<Self::Owned> {
        Some(self.val)
    }

    fn owned_ref_from_handle<'a>(&'a self, _handle: &'a Self::Handle) -> &'a Self::Owned {
        &self.val
    }
    fn owned_from_handle(self, _handle: Self::Handle) -> Self::Owned {
        self.val
    }

    fn handle_from_owned(_owned: &Self::Owned) -> Self::Handle {}

    fn reset_from_handle(&mut self, _handle: &Self::Handle) {}
}

impl<T: Hash + Eq> Key for Owned<T> {
    type Key = T;

    fn hash<S: BuildHasher>(&self, hash_builder: &S) -> u64 {
        hash_one(hash_builder, &self.val)
    }

    fn hash_owned<S: BuildHasher>(strong: &Self::Owned, hash_builder: &S) -> u64 {
        hash_one(hash_builder, strong)
    }

    fn eq_owned(&self, strong: &Self::Owned) -> bool {
        self.val.eq(strong)
    }

    fn eq_borrow<Q>(&self, key: &Q) -> bool
    where
        Q: ?Sized + Hash + Eq,
        Self::Key: Borrow<Q>,
    {
        self.val.borrow() == key
    }
}

/// A value that might need to store a persistent hash.
///
/// This is a `u64` for weak keys,
/// and a `()` everywhere else.
pub(crate) trait MaybeHash {
    /// Construct a new hash (or discard the input).
    fn new(hash: u64) -> Self;
}

impl MaybeHash for () {
    #[allow(clippy::unused_unit, clippy::semicolon_if_nothing_returned)]
    fn new(_hash: u64) -> Self {
        ()
    }
}
impl MaybeHash for u64 {
    fn new(hash: u64) -> Self {
        hash
    }
}

/// A weak element in a [`Table`](super::Table).
///
/// This is used internally to hold the values in a [`WeakValueKeyMap`](crate::WeakValueHashMap),
/// the keys in a [`WeakKeyHashMap`](crate::WeakKeyHashMap),
/// and _all_ elements in a [`WeakWeakHashMap`](crate::WeakWeakHashMap).
#[derive(Clone, Debug)]
pub(crate) struct Weak<T, H> {
    /// An instance of some [`WeakElement`].
    pub(crate) val: T,
    /// The computed hash of `val`, if this is a key.
    ///
    /// (We need to store this for weak keys,
    /// since if the `WeakElement` disappears,
    // we can no longer compute the same hash.)
    pub(crate) hash: H,
}

impl<T, H> Element for Weak<T, H>
where
    T: WeakElement,
    H: MaybeHash,
{
    type Owned = T::Strong;

    type Ref<'a>
        = T::Strong
    where
        Self: 'a;

    type Handle = T::Strong;
    type CachedHash = H;

    fn is_expired(&self) -> bool {
        self.val.is_expired()
    }

    fn as_ref(&self) -> Option<Self::Ref<'_>> {
        self.val.view()
    }

    fn handle(&self) -> Option<Self::Handle> {
        self.val.view()
    }

    fn from_owned(owned: Self::Owned, hash: H) -> (Self, Self::Handle) {
        (
            Weak {
                val: T::new(&owned),
                hash,
            },
            owned,
        )
    }

    fn into_owned(self) -> Option<Self::Owned> {
        self.val.view()
    }

    fn owned_ref_from_handle<'a>(&'a self, handle: &'a Self::Handle) -> &'a Self::Owned {
        handle
    }

    fn owned_from_handle(self, handle: Self::Handle) -> Self::Owned {
        handle
    }

    fn handle_from_owned(owned: &Self::Owned) -> Self::Handle {
        T::clone(owned)
    }

    fn reset_from_handle(&mut self, handle: &Self::Handle) {
        self.val = T::new(handle);
    }
}

impl<T> Key for Weak<T, u64>
where
    T: WeakKey,
{
    type Key = T::Key;

    fn hash<S: BuildHasher>(&self, _hash_builder: &S) -> u64 {
        self.hash
    }

    fn hash_owned<S: BuildHasher>(strong: &Self::Owned, hash_builder: &S) -> u64 {
        let mut h = hash_builder.build_hasher();
        T::hash(strong, &mut h);
        h.finish()
    }

    fn eq_owned(&self, strong: &Self::Owned) -> bool {
        if let Some(self_view) = self.val.view() {
            T::with_key(strong, |other_as_key| T::equals(&self_view, other_as_key))
        } else {
            false
        }
    }

    fn eq_borrow<Q>(&self, key: &Q) -> bool
    where
        Q: ?Sized + Hash + Eq,
        Self::Key: Borrow<Q>,
    {
        if let Some(self_view) = self.val.view() {
            T::equals(&self_view, key)
        } else {
            false
        }
    }
}
