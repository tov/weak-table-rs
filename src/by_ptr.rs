use std::ops::Deref;

use super::traits::*;

/// Wrapper struct for using pointer equality and hashes rather
/// than pointed-to value equality and hashes.
#[derive(Clone, Debug)]
pub struct ByPtr<K>(K);

impl<K: WeakElement> WeakElement for ByPtr<K> {
    type Strong = K::Strong;

    fn new(view: &Self::Strong) -> Self {
        ByPtr(K::new(view))
    }

    fn view(&self) -> Option<Self::Strong> {
        self.0.view()
    }
}

impl<K: WeakElement> WeakKey for ByPtr<K>
    where K::Strong: Deref
{
    type Key = *const <K::Strong as Deref>::Target;

    fn with_key<F, R>(view: &Self::Strong, f: F) -> R
        where F: FnOnce(&Self::Key) -> R
    {
        f(&(view.deref() as *const _))
    }
}

