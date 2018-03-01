use std::collections::hash_map::RandomState;
use std::hash::{BuildHasher, Hash};
use std::{rc, sync};

#[derive(Clone, Debug)]
pub struct WeakKeyHashMap<K, V, S = RandomState> {
    hash_builder: S,
    table: Box<[Option<(K, V, u64)>]>
}

const DEFAULT_INITIAL_CAPACITY: usize = 8;

fn new_boxed_slice<T>(size: usize) -> Box<[Option<T>]> {
    let mut vector = Vec::with_capacity(size);
    for _ in 0 .. size {
        vector.push(None)
    }
    vector.into_boxed_slice()
}

impl<K: WeakKey, V> WeakKeyHashMap<K, V, RandomState>
{
    /// Creates an empty `WeakHashmap`.
    pub fn new() -> Self {
        Self::with_capacity(DEFAULT_INITIAL_CAPACITY)
    }

    /// Creates an empty `WeakHashmap` with the given capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        WeakKeyHashMap {
            hash_builder: Default::default(),
            table: new_boxed_slice(capacity),
        }
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
            table: new_boxed_slice(capacity),
        }
    }

    /// Returns a reference to the map's `BuildHasher`.
    pub fn hasher(&self) -> &S {
        &self.hash_builder
    }

    /// Returns the number of elements the map can hold without reallocating.
    pub fn capacity(&self) -> usize {
        self.table.len()
    }
}

/// Interface for elements that can be stored in a weak hash table.
pub trait WeakElement {
    /// The type at which a weak element can be viewed.
    ///
    /// For example, for `std::rc::Weak<T>`, this will be `std::rc::Rc<T>`.
    type Strong;

    /// Constructs a new weak element from a strong view.
    fn new(view: &Self::Strong) -> Self;

    /// Acquires a strong version of the weak element.
    fn view(&self) -> Option<Self::Strong>;

    /// Is the given weak element expired?
    fn expired(&self) -> bool {
        self.view().is_none()
    }
}

/// Interface for elements that can act as keys in weak hash tables.
pub trait WeakKey : WeakElement {
    /// The underlying key type.
    ///
    /// For example, for `std::rc::Weak<T>`, this will be `T`.
    type Key: Eq + Hash;

    /// Borrows a view of the key.
    fn view_key(view: &Self::Strong) -> &Self::Key;
}

impl<T> WeakElement for rc::Weak<T> {
    type Strong = rc::Rc<T>;

    fn new(view: &Self::Strong) -> Self {
        rc::Rc::<T>::downgrade(view)
    }

    fn view(&self) -> Option<Self::Strong> {
        self.upgrade()
    }
}

impl<T: Eq + Hash> WeakKey for rc::Weak<T> {
    type Key = T;

    fn view_key(view: &Self::Strong) -> &Self::Key {
        &view
    }
}

impl<T> WeakElement for sync::Weak<T> {
    type Strong = sync::Arc<T>;

    fn new(view: &Self::Strong) -> Self {
        sync::Arc::<T>::downgrade(view)
    }

    fn view(&self) -> Option<Self::Strong> {
        self.upgrade()
    }
}

impl<T: Eq + Hash> WeakKey for sync::Weak<T> {
    type Key = T;

    fn view_key(view: &Self::Strong) -> &Self::Key {
        &view
    }
}
