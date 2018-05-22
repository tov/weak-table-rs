//! Traits for describing strong and weak pointers and their use as elements and keys.
//!
//! These traits provide mechanisms for converting between weak and strong pointers
//! ([`WeakElement`](trait.WeakElement.html)) and for dereferencing strong pointers
//! ([`WeakKey`](trait.WeakKey.html)). Implementations of these traits are provided for
//! `std::rc::Weak` and `std::sync::Weak`. If you would like to use your own pointer type
//! as a weak element, you need to implement `WeakElement` for your weak pointer type; to use it
//! as a weak key, implement `WeakKey` as well.

use std::hash::Hash;
use std::{rc, sync};

/// Interface for elements that can be stored in weak hash tables.
///
/// This trait applies to the weak version of a reference-counted pointer; it can be used to
/// convert a weak pointer into a strong pointer and back. For example, the impl for
/// `std::rc::Weak<T>` defines the `Strong` associated type as `std::rc::Rc<T>`. Then method
/// `new` can be used to downgrade an `Rc<T>` to a `Weak<T>`, and method `view` can be used to
/// upgrade a `Weak<T>` into an `Rc<T>`, if it's still alive. If we think of the weak pointer as
/// what is stored, then the strong pointer is a temporary view of it.
pub trait WeakElement {
    /// The type at which a weak element can be viewed.
    ///
    /// For example, for `std::rc::Weak<T>`, this will be `std::rc::Rc<T>`.
    type Strong;

    /// Constructs a weak pointer from a strong pointer.
    ///
    /// This is usually implemented by a `downgrade` method.
    fn new(view: &Self::Strong) -> Self;

    /// Acquires a strong pointer from a weak pointer.
    ///
    /// This is usually implemented by an `upgrade` method.
    fn view(&self) -> Option<Self::Strong>;

    /// Is the given weak element expired?
    ///
    /// The default implemention checks whether a strong pointer can be obtained via `view`.
    fn is_expired(&self) -> bool {
        self.view().is_none()
    }

    /// Clones a strong pointer.
    ///
    /// The default implementation uses `new` and `view`; you should override it.
    fn clone(view: &Self::Strong) -> Self::Strong
        where Self: Sized
    {
        Self::new(view).view().expect("WeakElement::clone")
    }
}

/// Interface for elements that can act as keys in weak hash tables.
///
/// To use an element as a weak hash map key or weak hash set element), the hash table
/// needs to be able to view the actual key values to hash and compare them. This trait
/// provides the necessary mechanism.
pub trait WeakKey : WeakElement {
    /// The underlying key type.
    ///
    /// For example, for `std::rc::Weak<T>`, this will be `T`.
    type Key: ?Sized + Eq + Hash;

    /// Allows borrowing a view of the key, via a callback.
    ///
    /// Rather than returning a borrowed reference to the actual key, this method passes a
    /// reference to the key to a callback with an implicit higher-order lifetime bound. This is
    /// necessary to get the lifetimes right in cases where the key is not actually store in the
    /// strong pointer.
    fn with_key<F, R>(view: &Self::Strong, f: F) -> R
        where F: FnOnce(&Self::Key) -> R;
}

impl<T: ?Sized> WeakElement for rc::Weak<T> {
    type Strong = rc::Rc<T>;

    fn new(view: &Self::Strong) -> Self {
        rc::Rc::<T>::downgrade(view)
    }

    fn view(&self) -> Option<Self::Strong> {
        self.upgrade()
    }

    fn clone(view: &Self::Strong) -> Self::Strong {
        view.clone()
    }
}

impl<T: ?Sized + Eq + Hash> WeakKey for rc::Weak<T> {
    type Key = T;

    fn with_key<F, R>(view: &Self::Strong, f: F) -> R
        where F: FnOnce(&Self::Key) -> R
    {
        f(&view)
    }
}

impl<T: ?Sized> WeakElement for sync::Weak<T> {
    type Strong = sync::Arc<T>;

    fn new(view: &Self::Strong) -> Self {
        sync::Arc::<T>::downgrade(view)
    }

    fn view(&self) -> Option<Self::Strong> {
        self.upgrade()
    }

    fn clone(view: &Self::Strong) -> Self::Strong {
        view.clone()
    }
}

impl<T: ?Sized + Eq + Hash> WeakKey for sync::Weak<T>
{
    type Key = T;

    fn with_key<F, R>(view: &Self::Strong, f: F) -> R
        where F: FnOnce(&Self::Key) -> R
    {
        f(&view)
    }
}

