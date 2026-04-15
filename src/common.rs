//! Macros that expand into common types and functions.
//!
//! We use these to limit duplicated code.

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

/// Declare set-algebra iterator methods on a set type.
macro_rules! set_op_methods {
    {$settype:ident} => {
        /// Returns an iterator that computes the intersection of this set
        /// with `other`.
        ///
        /// This iterator will return exactly the set of elements
        /// that are present in both sets.
        ///
        /// It is not specified which set the elements will be copied from.
        ///
        /// *O*(*1*) time to construct the iterator.
        ///
        /// Consuming the iterator will run in *O*(*n*) expected time and *O*(*n* *p)
        /// worst-case time, where *n* is the size of the _smaller_ set, and *p*
        /// is the average probe length in the _larger_ set.
        pub fn intersection<'a>(&'a self, other: &'a $settype<T, S>) -> Intersection<'a, T, S> {
            let (small, large) = sort_by_size(self, other);
            Intersection {
                iter: small.iter(),
                other: large
            }
        }

        /// Returns an iterator that computes the difference of this set
        /// and `other`.
        ///
        /// This iterator will return exactly the set of elements
        /// that are present in `self`, but not in `other`.
        ///
        /// *O*(*1*) time to construct the iterator.
        ///
        /// Consuming the iterator will run in *O*(*n*) expected time and *O*(*n* *p*)
        /// worst-case time, where *n* is the size of `self`, and *p*
        /// is the average probe length in `other`.
        pub fn difference<'a>(&'a self, other: &'a $settype<T, S>) -> Difference<'a, T, S> {
            Difference {
                iter: self.iter(),
                other
            }
        }

        /// Returns an iterator over that computes the union of this set and
        /// `other`.
        ///
        /// This iterator will return exactly the set of elements that are
        /// present in either of `self` or `other`.  No element will be returned
        /// more than once.
        ///
        /// If an element is present in both sets, it is not specified which set
        /// it will be copied from.
        ///
        /// *O*(*1*) time to construct the iterator.
        ///
        /// Consuming the iterator will run in *O*(*n* + *m*) expected time and
        /// *O*(*n* + *m* *p*) worst-case time, where *n* is the size of the
        /// larger set, *m* is the size of the smaller set, and *p* is
        /// the average probe length.
        pub fn union<'a>(&'a self, other: &'a $settype<T, S>) -> Union<'a, T, S> {
            let (small, large) = sort_by_size(self, other);
            Union {
                iter: large.iter().chain(small.difference(large))
            }
        }

        /// Returns an iterator over that computes the symmetric difference of
        ///  this set and `other`.
        ///
        /// This iterator will return exactly the set of elements that are
        /// present in exactly one of `self` or `other` but not both.
        ///
        /// *O*(*1*) time to construct the iterator.
        ///
        /// Consuming the iterator will run in *O*(*n* + *m*) expected time and
        /// *O*((*n* + *m*)*p*) worst-case time, where *n* is the size of `self`
        /// *m* is the size of `other`, and *p* is the average probe length.
        pub fn symmetric_difference<'a>(&'a self, other: &'a $settype<T, S>) -> SymmetricDifference<'a, T, S> {
            SymmetricDifference {
                iter: self.difference(other).chain(other.difference(self))
            }
        }
    }
}
pub(crate) use set_op_methods;

/// Declare set-albegra operations on a set type.
macro_rules! set_op_types {
    {$settype:ident where {$($wheres:tt)+} } => {
        /// An iterator to return the intersection of two sets.
        pub struct Intersection<'a, T, S> {
            /// An iterator of items in the smaller set.
            iter: Iter<'a, T>,

            /// The other set; we only return items from `iter`
            /// if they are in this set too.
            other: &'a $settype<T, S>,
        }

        impl<'a, T, S: BuildHasher> Iterator for Intersection<'a, T, S>
            where $($wheres)+
        {
            type Item = T::Strong;

            fn next(&mut self) -> Option<Self::Item> {
                for item in &mut self.iter {
                    if self.other.contains_strong(&item) {
                        return Some(item);
                    }
                }
                return None
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (0, self.iter.size_hint().1)
            }
        }

        /// An iterator to return the difference of two sets.
        pub struct Difference<'a, T, S> {
            /// An iterator over the items that we might be returning.
            iter: Iter<'a, T>,

            /// The other set.  If elements are in this set,
            /// we don't yield them.
            other: &'a $settype<T, S>,
        }

        impl<'a, T, S: BuildHasher> Iterator for Difference<'a, T, S>
            where $($wheres)+
        {
            type Item = T::Strong;

            fn next(&mut self) -> Option<Self::Item> {
                for item in &mut self.iter {
                    if ! self.other.contains_strong(&item) {
                        return Some(item);
                    }
                }
                return None
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (0, self.iter.size_hint().1)
            }
        }

        /// An iterator to return the union of two sets.
        pub struct Union<'a, T, S> {
            /// The underlying iterator.
            iter: iter::Chain<Iter<'a, T>, Difference<'a, T, S>>,
        }

        impl<'a, T, S:BuildHasher> Iterator for Union<'a, T, S>
            where $($wheres)+
        {
            type Item = T::Strong;

            fn next(&mut self) -> Option<Self::Item> {
                self.iter.next()
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.iter.size_hint()
            }
        }

        /// An iterator to return the symmetric difference of two sets.
        pub struct SymmetricDifference<'a, T, S> {
            /// The underlying iterator.
            iter: iter::Chain<Difference<'a, T, S>, Difference<'a, T, S>>,
        }

        impl<'a, T, S:BuildHasher> Iterator for SymmetricDifference<'a, T, S>
            where $($wheres)+
        {
            type Item = T::Strong;

            fn next(&mut self) -> Option<Self::Item> {
                self.iter.next()
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                self.iter.size_hint()
            }
        }
    }
}
pub(crate) use set_op_types;

/// Implement an operator trait for a set type.
macro_rules! single_set_op {
    { $settype:ident where {$($wheres:tt)+}
       op: $op:ident,
       method: $method:ident,
       set_method: $set_method:ident $(,)?
    } => {
        impl<T, S: BuildHasher + Default> ops::$op<&$settype<T, S>> for &$settype<T, S>
            where $($wheres)+
        {
            type Output = $settype<T, S>;

            fn $method(self, other: &$settype<T,S>) -> Self::Output {
                self.$set_method(other).collect()
            }
        }
    }
}
pub(crate) use single_set_op;

/// Implement operator traits for a set type.
macro_rules! set_operators {
    {$settype:ident where {$($wheres:tt)+} } => {
        single_set_op!{
            $settype where {$($wheres)+}
            op: BitAnd,
            method: bitand,
            set_method: intersection
        }
        single_set_op!{
            $settype where {$($wheres)+}
            op: BitOr,
            method: bitor,
            set_method: union
        }
        single_set_op!{
            $settype where {$($wheres)+}
            op: BitXor,
            method: bitxor,
            set_method: symmetric_difference
        }
        single_set_op!{
            $settype where {$($wheres)+}
            op: Sub,
            method: sub,
            set_method: difference
        }
    }
}
pub(crate) use set_operators;

/// Declare relationship-checking member functions for set types.
macro_rules! set_relationships {
    {$settype:ident} => {
        /// Returns true if every element of `other` is a also a member
        /// of this set.
        pub fn is_superset(&self, other: &$settype<T, S>) -> bool {
            other.is_subset(self)
        }

        /// Returns true if this set has no members in common with `other`.
        pub fn is_disjoint(&self, other: &$settype<T, S>) -> bool {
            let (small, large) = sort_by_size(self, other);
            ! small.iter().any(|t| large.contains_strong(&t))
        }
    }
}
pub(crate) use set_relationships;

/// Declare members that every container has, which don't require constraining
/// the members of the container.
macro_rules! universal_hashless_members {
    ($container:ident ($cname:expr, a $shortname:expr) $constructor:path { $($params:ident),* } ) => {
        impl<$($params),*> $container<$($params),* , RandomState> {
            #[doc=concat!("Creates an empty ", $cname, ".")]
            ///
            /// *O*(1) time
            pub fn new() -> Self {
                Self::with_capacity(crate::size_policy::DEFAULT_INITIAL_CAPACITY)
            }

            #[doc=concat!("Creates an empty ", $cname, " with the given capacity.")]
            ///
            /// *O*(*n*) time
            pub fn with_capacity(capacity: usize) -> Self {
                Self::with_capacity_and_hasher(capacity, Default::default())
            }
        }

        impl<$($params),*, S: BuildHasher> $container<$($params),* , S> {
            #[doc=concat!("Creates an empty ", $cname, " with the given hasher.")]
            ///
            /// *O*(*n*) time
            pub fn with_hasher(hash_builder: S) -> Self {
                Self::with_capacity_and_hasher(crate::size_policy::DEFAULT_INITIAL_CAPACITY, hash_builder)
            }

            #[doc=concat!("Creates an empty ", $cname, " with the given capacity and hasher.")]
            ///
            /// *O*(*n*) time
            pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
                Self($constructor(capacity, hash_builder))
            }
        }

        impl<$($params),*, S: BuildHasher + Default> Default for $container<$($params),* , S> {
            fn default() -> Self {
                Self::with_hasher(Default::default())
            }
        }

        impl<$($params),*, S> $container<$($params),* , S> {
            #[doc=concat!("Returns a reference to the ",$shortname, "'s `BuildHasher`.")]
            ///
            ///
            /// *O*(1) time
            pub fn hasher(&self) -> &S {
                self.0.hasher()
            }

            #[doc=concat!("Returns the number of elements the ",$shortname," can hold without reallocating.")]
            ///
            /// *O*(1) time
            pub fn capacity(&self) -> usize {
                self.0.capacity()
            }


            /// Returns an over-approximation of the number of elements.
            ///
            /// (This is an over-approximation because it includes expired elements.)
            ///
            /// *O*(1) time
            pub fn len(&self) -> usize {
                self.0.len()
            }

            #[doc=concat!("Is the ",$shortname," empty?")]
            ///
            ///
            /// Note that this may return false even if all elements have
            /// expired, if they haven't been collected yet.
            ///
            /// *O*(1) time
            pub fn is_empty(&self) -> bool {
                self.len() == 0
            }


            /// Returns proportion of buckets that are used.
            ///
            /// This is an over-approximation because of expired elements.
            ///
            /// *O*(1) time
            pub fn load_factor(&self) -> f32 {
                self.0.load_factor()
            }


            #[doc=concat!("Remove all elements from the ",$shortname,".")]
            ///
            /// *O*(*n*) time
            pub fn clear(&mut self) {
                self.0.clear();
            }
        }
    }
}
pub(crate) use universal_hashless_members;
