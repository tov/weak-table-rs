//! Macros to declare common functionality for map types.

/// Declare IntoKeys and IntoValues iterator types for a map.
macro_rules! into_kv_types {
    {$ktype:ty, $vtype:ty where {$($wheres:tt)+}} => {
        /// A consuming iterator that returns only keys, and discards values.
        pub struct IntoKeys<K, V>(IntoIter<K,V>);

        impl<K,V> Iterator for IntoKeys<K,V> where $($wheres)+ {
            type Item = $ktype;

            fn next(&mut self)  -> Option<Self::Item> {
                self.0.next().map(|(k, _)| k)
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.0.size_hint()
            }
        }

        /// A consuming iterator that returns only values, and discards keys.
        pub struct IntoValues<K, V>(IntoIter<K,V>);

        impl<K,V> Iterator for IntoValues<K,V> where $($wheres)+ {
            type Item = $vtype;

            fn next(&mut self)  -> Option<Self::Item> {
                self.0.next().map(|(_, v)| v)
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.0.size_hint()
            }
        }
    }
}
pub(crate) use into_kv_types;

/// Construct into_keys and into_values methods for a map.
macro_rules! into_kv_methods {
    {} => {
        /// Returns an iterator that owns and consumes this map,
        /// returning the keys in the map.
        ///
        /// *O*(*1*)
        pub fn into_keys(self) -> IntoKeys<K,V> {
            IntoKeys(self.into_iter())
        }

        /// Returns an iterator that owns and consumes this map,
        /// returning the keys in the map.
        ///
        /// *O*(*1*)
        pub fn into_values(self) -> IntoValues<K,V> {
            IntoValues(self.into_iter())
        }
    }
}
pub(crate) use into_kv_methods;

/// Construct into_keys and into_values methods for a ptr map.
macro_rules! ptr_into_kv_methods {
    {} => {
        /// Returns an iterator that owns and consumes this map,
        /// returning the keys in the map.
        ///
        /// *O*(*1*)
        pub fn into_keys(self) -> IntoKeys<ByPtr<K>, V> {
            self.0.into_keys()
        }

        /// Returns an iterator that owns and consumes this map,
        /// returning the keys in the map.
        ///
        /// *O*(*1*)
        pub fn into_values(self) -> IntoValues<ByPtr<K>, V> {
            self.0.into_values()
        }
    }
}
pub(crate) use ptr_into_kv_methods;
