use std::{
    borrow::Borrow,
    hash::{BuildHasher, Hash, Hasher},
};

use crate::traits::{WeakElement, WeakKey};

pub(crate) trait Element: Sized {
    type Owned;
    type Ref<'a>
    where
        Self: 'a;
    type Upgraded;
    type CachedHash: MaybeHash;

    fn as_ref<'a>(&'a self) -> Option<Self::Ref<'a>>;

    fn is_expired(&self) -> bool;

    fn upgrade(&self) -> Option<Self::Upgraded>;

    fn from_owned(owned: Self::Owned, cached_hash: Self::CachedHash) -> (Self, Self::Upgraded);

    fn into_owned(self) -> Option<Self::Owned>;

    fn owned_ref_from_upgrade<'a>(&'a self, upgraded: &'a Self::Upgraded) -> &'a Self::Owned;

    fn owned_from_upgrade(self, upgraded: Self::Upgraded) -> Self::Owned;

    fn upgraded_from_owned(owned: &Self::Owned) -> Self::Upgraded;

    fn reset_from_upgrade(&mut self, _upgraded: &Self::Upgraded);
}

pub(crate) trait Key: Element + Sized {
    type Key: ?Sized;

    fn hash<S: BuildHasher>(&self, hash_builder: &S) -> u64;

    fn hash_owned<S: BuildHasher>(strong: &Self::Owned, hash_builder: &S) -> u64;

    fn eq_owned(&self, strong: &Self::Owned) -> bool;

    fn eq_borrow<Q>(&self, key: &Q) -> bool
    where
        Q: ?Sized + Hash + Eq,
        Self::Key: Borrow<Q>;
}

#[derive(Clone, Debug)]
pub(crate) struct Owned<T> {
    pub(crate) val: T,
}

impl<T> Element for Owned<T> {
    type Owned = T;
    type Ref<'a>
        = &'a T
    where
        T: 'a;
    type Upgraded = ();
    type CachedHash = ();

    fn is_expired(&self) -> bool {
        false
    }

    fn as_ref(&self) -> Option<Self::Ref<'_>> {
        Some(&self.val)
    }
    fn upgrade(&self) -> Option<Self::Upgraded> {
        Some(())
    }

    fn from_owned(val: Self::Owned, _hash: ()) -> (Self, Self::Upgraded) {
        (Owned { val }, ())
    }

    fn into_owned(self) -> Option<Self::Owned> {
        Some(self.val)
    }

    fn owned_ref_from_upgrade<'a>(&'a self, _upgraded: &'a Self::Upgraded) -> &'a Self::Owned {
        &self.val
    }
    fn owned_from_upgrade(self, _upgraded: Self::Upgraded) -> Self::Owned {
        self.val
    }

    fn upgraded_from_owned(_owned: &Self::Owned) -> Self::Upgraded {}

    fn reset_from_upgrade(&mut self, _upgraded: &Self::Upgraded) {}
}

impl<T: Hash + Eq> Key for Owned<T> {
    type Key = T;

    fn hash<S: BuildHasher>(&self, hash_builder: &S) -> u64 {
        hash_builder.hash_one(&self.val)
    }

    fn hash_owned<S: BuildHasher>(strong: &Self::Owned, hash_builder: &S) -> u64 {
        hash_builder.hash_one(strong)
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

pub(crate) trait MaybeHash {
    fn new(hash: u64) -> Self;
}

impl MaybeHash for () {
    #[allow(clippy::unused_unit)]
    fn new(_hash: u64) -> Self {
        ()
    }
}
impl MaybeHash for u64 {
    fn new(hash: u64) -> Self {
        hash
    }
}

#[derive(Clone, Debug)]
pub(crate) struct Weak<T, H> {
    pub(crate) val: T,
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

    type Upgraded = T::Strong;
    type CachedHash = H;

    fn is_expired(&self) -> bool {
        self.val.is_expired()
    }

    fn as_ref<'a>(&'a self) -> Option<Self::Ref<'a>> {
        self.val.view()
    }

    fn upgrade(&self) -> Option<Self::Upgraded> {
        self.val.view()
    }

    fn from_owned(owned: Self::Owned, hash: H) -> (Self, Self::Upgraded) {
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

    fn owned_ref_from_upgrade<'a>(&'a self, upgraded: &'a Self::Upgraded) -> &'a Self::Owned {
        upgraded
    }

    fn owned_from_upgrade(self, upgraded: Self::Upgraded) -> Self::Owned {
        upgraded
    }

    fn upgraded_from_owned(owned: &Self::Owned) -> Self::Upgraded {
        T::clone(owned)
    }

    fn reset_from_upgrade(&mut self, upgraded: &Self::Upgraded) {
        self.val = T::new(upgraded);
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
        self.val.view().is_some_and(|self_view| {
            T::with_key(strong, |other_as_key| T::equals(&self_view, other_as_key))
        })
    }

    fn eq_borrow<Q>(&self, key: &Q) -> bool
    where
        Q: ?Sized + Hash + Eq,
        Self::Key: Borrow<Q>,
    {
        self.val
            .view()
            .is_some_and(|self_view| T::equals(&self_view, key))
    }
}
