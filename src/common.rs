//! Macros that expand into common types and functions.
//!
//! We use these to limit duplicated code.

mod map;
mod set;

pub(crate) use map::*;
pub(crate) use set::*;

/// Declare members that every container has, which don't require constraining
/// the members of the container.
macro_rules! universal_hashless_members {
    ($container:ident ($cname:expr, a $shortname:expr) $constructor:path { $($params:ident),* } ) => {
        #[cfg(any(test, feature = "std", feature = "ahash"))]
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

/// Declare members that all of our containers have,
/// and that depend on the K,V parameters being appropriately constrained,
/// but which don't take or return any elements.
macro_rules! universal_key_independent_members {
    {$elts:expr} => {
        #[doc=concat!("Removes all ", $elts, " whose keys have expired.")]
        ///
        /// *O*(*n*) time
        pub fn remove_expired(&mut self) {
            self.0.remove_expired();
        }

        /// Reserves room for additional elements.
        ///
        /// This method ensures that at least `additional_capacity` insertions
        /// may be performed without reallocating.
        ///
        /// *O*(*n*) time
        pub fn reserve(&mut self, additional_capacity: usize) {
            self.try_reserve(additional_capacity)
                .expect("Unable to reserve additional capacity");
        }

        #[doc=concat!("Tries to reserve room for additional ", $elts, ".")]
        ///
        /// If this method succeeds, then at least `additional_capacity` insertions
        /// may be performed without reallocating further.
        ///
        /// *O*(*n*) time
        pub fn try_reserve(
            &mut self,
            additional_capacity: usize,
        ) -> Result<(), crate::TryReserveError> {
            self.0.try_reserve(additional_capacity)
        }

        #[doc=concat!("Shrinks the capacity to the minimum to hold the current number of ", $elts, ".")]
        ///
        /// *O*(*n*) time
        pub fn shrink_to_fit(&mut self) {
            self.0.shrink_to_fit();
        }

        #[doc=concat!("Shrinks the capacity to hold no fewer than `min_capacity` ", $elts, ".")]
        ///
        /// May remove expired items if necessary.
        /// Does nothing if the current capacity is already at `min_capacity` or below.
        ///
        /// *O*(*n*) time
        pub fn shrink_to(&mut self, min_capacity: usize) {
            self.0.shrink_to(min_capacity);
        }
    }
}
pub(crate) use universal_key_independent_members;
