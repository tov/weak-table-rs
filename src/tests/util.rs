//! Testing utility types and functions

use crate::compat::*;

/// A Vec wrapper that pretends to be a set for debugging purposes.
///
/// We use this to test our debug implementations.
///
/// (We can't compare against expected strings,
/// since sort order is arbitrary, and the actual debug format is unstable.)
pub(crate) struct VecDebugAsSet<T>(pub(crate) Vec<T>);

impl<T: Debug> fmt::Debug for VecDebugAsSet<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.0.iter()).finish()
    }
}

impl<T> FromIterator<T> for VecDebugAsSet<T> {
    fn from_iter<IT: IntoIterator<Item = T>>(iter: IT) -> Self {
        VecDebugAsSet(iter.into_iter().collect())
    }
}

/// A Vec wrapper that pretends to be a map for debugging purposes.
///
/// We use this to test our debug implementations.
///
/// (We can't compare against expected strings,
/// since sort order is arbitrary, and the actual debug format is unstable.)
pub(crate) struct VecDebugAsMap<K, V>(pub(crate) Vec<(K, V)>);

impl<K: Debug, V: Debug> fmt::Debug for VecDebugAsMap<K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_map()
            .entries(self.0.iter().map(|(k, v)| (k, v)))
            .finish()
    }
}

impl<K, V> FromIterator<(K, V)> for VecDebugAsMap<K, V> {
    fn from_iter<IT: IntoIterator<Item = (K, V)>>(iter: IT) -> Self {
        VecDebugAsMap(iter.into_iter().collect())
    }
}
