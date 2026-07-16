//! Macros for tests that work the same way across all types.

/// Tests for common constructor functions.
macro_rules! empty_constructor_tests {
    {$container:ty} => {
        #[test]
        fn new_empty() {
            let arry: [$container; 5] = [
                <$container>::new(),
                Default::default(),
                <$container>::with_capacity(0),
                <$container>::with_hasher(Default::default()),
                <$container>::from([]),
            ];
            for x in arry {
                assert!(x.is_empty());
                assert_eq!(x.len(), 0);
                assert_eq!(x.capacity(), 0);
                assert_eq!(x.load_factor(), 0.0);
            }
        }

        #[test]
        fn new_empty_with_capacity() {
            let arry: [$container; 2] = [
                <$container>::with_capacity(128),
                <$container>::with_capacity_and_hasher(128, Default::default()),
            ];
            for x in arry {
                assert!(x.is_empty());
                assert_eq!(x.len(), 0);
                assert!((128..=384).contains(&x.capacity()));
                assert_eq!(x.load_factor(), 0.0);
            }
        }

        #[test]
        fn new_empty_with_hasher() {
            let h = crate::compat::RandomState::default();
            let hash_of_seventeen = crate::util::hash_one(&h, &17_u32);
            let arry: [$container; 2] = [
                <$container>::with_hasher(h.clone()),
                <$container>::with_capacity_and_hasher(0, h.clone())
            ];
            for x in arry {
                assert_eq!(x.len(), 0);
                assert_eq!(
                    crate::util::hash_one(x.hasher(), &17_u32),
                    hash_of_seventeen
                );
            }
        }
    }
}
pub(crate) use empty_constructor_tests;
