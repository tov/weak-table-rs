use std::borrow::Borrow;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

#[derive(Clone, Debug)]
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

