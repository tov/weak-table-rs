//! Set operation tests for WeakHashSet and PtrWeakHashSet.

/// Tests for general set algebra functionality.
macro_rules! set_operation_tests {
    {$container:ident, $by_ptr:expr} => {

        #[test]
        fn set_operations() {
            use crate::compat::Vec;

            type Set = $container<Weak<u32>>;
            assert!($by_ptr == 0 || $by_ptr == 1);
            // If by_ptr is true, this is just vec of 100 distinct zeroes.
            let ns: Vec<Rc<u32>> = (0..100).map(|n| Rc::new(n * (1-$by_ptr))).collect();
            let numbers: Set = ns.iter().cloned().collect();
            let evens: Set = (0..100)
                .filter_map(|n| (n % 2 == 0).then(|| ns[n].clone()))
                .collect();
            let odds: Set = (0..100)
                .filter_map(|n| (n % 2 == 1).then(|| ns[n].clone()))
                .collect();
            let squares: Set = (0..10)
                .map(|n| ns[n*n].clone())
                .collect();
            let primes: Set = [
                2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37,
                41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97
            ]
            .map(|n| ns[n].clone())
            .into();

            assert!(evens.is_subset(&numbers));
            assert!(odds.is_subset(&numbers));
            assert!(numbers.is_superset(&evens));
            assert!(numbers.is_superset(&odds));

            assert!(!odds.is_subset(&evens));
            assert!(!odds.is_subset(&primes));
            assert!(!odds.is_superset(&evens));
            assert!(!odds.is_superset(&primes));

            assert!(odds.is_disjoint(&evens));
            assert!(primes.is_disjoint(&squares));
            assert!(evens.is_disjoint(&odds));
            assert!(squares.is_disjoint(&primes));
            assert!(!primes.is_disjoint(&odds));
            assert!(!primes.is_disjoint(&evens));

            // union
            assert_eq!(numbers, &evens | &odds);
            assert_eq!(evens.union(&odds).count(), numbers.len());

            // intersection
            let two = Set::from([ns[2].clone()]);
            assert_eq!(two, &evens & &primes);
            assert_eq!(two, &primes & &evens);
            assert_eq!(evens.intersection(&primes).count(), 1);

            // disjunction
            assert!((&primes - &two).is_subset(&odds));
            assert!((&two - &primes).is_empty());
            assert_eq!(&primes - &squares, primes);
            assert_eq!(&primes - &evens, &primes & &odds);
            assert_eq!(
                (&primes - &two).iter().count(),
                primes.difference(&two).count()
            );

            // symmetric difference
            assert_eq!(&evens ^ &odds, numbers);
            assert_eq!(&evens ^ &squares,
                &(&evens - &squares) | &(&squares - &evens)
            );
            assert_eq!(
                evens.symmetric_difference(&odds).count(),
                numbers.len()
            );
            assert_eq!(
                evens.symmetric_difference(&squares).count(),
                (&evens ^ &squares).len()
            );
        }
    }
}
pub(crate) use set_operation_tests;
