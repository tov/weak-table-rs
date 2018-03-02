use std::borrow::Borrow;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

#[derive(Clone)]
pub struct RcKey<K>(pub Rc<K>);

impl<K: PartialEq> PartialEq for RcKey<K> {
    fn eq(&self, other: &RcKey<K>) -> bool {
        *self.0 == *other.0
    }
}

impl<K: Eq> Eq for RcKey<K> { }

impl<K: Hash> Hash for RcKey<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (*self.0).hash(state);
    }
}

impl<K> Borrow<K> for RcKey<K> {
    fn borrow(&self) -> &K {
        &*self.0
    }
}

impl<K: fmt::Debug> fmt::Debug for RcKey<K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (*self.0).fmt(f)
    }
}
