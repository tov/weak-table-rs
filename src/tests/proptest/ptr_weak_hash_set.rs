use crate as weak_table2;
use crate::tests::proptest::KeyByPtr;

use crate::compat::{
    sync::{Arc, Weak},
    *,
};
use core::marker::PhantomData;

use quickcheck::quickcheck;

use weak_table2::PtrWeakHashSet;

use super::{ExecuteMapCmd, ForgetStrategy, InsertStrategy, MapScript, RemoveStrategy};

fn test_script<K, V>(script: &MapScript<K, V>) -> bool
where
    K: Clone + Debug + Eq + Hash + Ord,
    V: Clone + Debug + Eq + Ord,
{
    let mut tester = Tester::with_capacity(4);
    tester.execute_script(script);
    tester.check()
}

quickcheck! {
    fn prop_u8_u8(script: MapScript<u8, u8>) -> bool {
        test_script(&script)
    }

    fn prop_string_usize(script: MapScript<String, usize>) -> bool {
        test_script(&script)
    }
}
#[derive(Clone, Debug)]
pub struct Tester<K: Hash + Eq, V> {
    weak: PtrWeakHashSet<Weak<K>>,
    strong: HashSet<KeyByPtr<K>>,
    log: Vec<Weak<K>>,

    _phantom: PhantomData<V>,
}

impl<K, V> Tester<K, V>
where
    K: Hash + Eq + Clone + Debug + Ord,
{
    pub fn with_capacity(capacity: usize) -> Self {
        Tester {
            weak: PtrWeakHashSet::with_capacity(capacity),
            strong: HashSet::default(),
            log: Vec::new(),
            _phantom: PhantomData,
        }
    }

    #[allow(clippy::cognitive_complexity)]
    pub fn check(&self) -> bool {
        // We'll use a variety of accessors here to make sure they give us
        // similar answers.

        // Check length accessors.
        assert!(self.weak.len() >= self.strong.len());
        {
            let mut weak2 = self.weak.clone();
            weak2.remove_expired();
            assert_eq!(weak2.len(), self.strong.len());
        }
        #[allow(clippy::len_zero)]
        {
            assert_eq!(self.weak.is_empty(), self.weak.len() == 0);
        }

        // Check capacity is plausible.
        assert!(self.weak.capacity() >= self.weak.len());

        // Construct new versions of weak table in several ways; make sure they are the same.
        {
            let weak2: PtrWeakHashSet<Weak<K>> = self.strong.iter().map(|v| v.0.clone()).collect();
            assert_eq!(&weak2, &self.weak);
            assert!(weak2.is_subset(&self.weak));
            assert!(self.weak.is_subset(&weak2));

            let weak3 = weak2.clone();
            assert_eq!(&weak3, &self.weak);
        }

        // Use contains functionality to test for matches.
        {
            for k in self.weak.iter() {
                assert!(self.strong.contains(&KeyByPtr(k.clone())));
            }
            for k in self.strong.iter() {
                assert!(self.weak.contains(&k.0));
            }
        }

        // Use a few other iterator types to construct a version of the strong
        // table.
        {
            let weak2 = self.weak.clone();
            let copy: HashSet<_> = weak2.into_iter().map(KeyByPtr).collect();
            assert_eq!(copy, self.strong);

            let mut weak3 = self.weak.clone();
            let copy: HashSet<_> = weak3.drain().map(KeyByPtr).collect();
            assert_eq!(copy, self.strong);
            assert!(weak3.is_empty());

            let copy: HashSet<_> = (&self.weak).into_iter().map(KeyByPtr).collect();
            assert_eq!(copy, self.strong);
        }

        // Construct version of strong table, make sure it is the same.
        let copy = self.weak.iter().map(KeyByPtr).collect();
        if self.strong == copy {
            //            eprintln!("Tester::check: succeeded: {:?}", self.weak);
            true
        } else {
            eprintln!("Tester::check: failed: {:?} ≠ {:?}", self.strong, copy);
            false
        }
    }

    fn nth_key_mod_len(&self, n: usize) -> Option<Arc<K>> {
        if self.log.is_empty() {
            None
        } else {
            Weak::upgrade(&self.log[n % self.log.len()])
        }
    }

    #[allow(clippy::needless_pass_by_value)]
    fn insert_impl(&mut self, strategy: InsertStrategy, key_ptr: Arc<K>, _value: &V, log: bool) {
        match strategy {
            InsertStrategy::ViaEntry | InsertStrategy::ViaInsert => {
                let _ = self.weak.insert(key_ptr.clone());
            }
            InsertStrategy::ViaExtend | InsertStrategy::ViaExtendRef => {
                let lst = [key_ptr.clone()];
                self.weak.extend(lst);
            }
        }
        let strong_key = KeyByPtr(key_ptr.clone());
        self.strong.remove(&strong_key);
        self.strong.insert(strong_key);
        if log {
            self.log.push(Arc::downgrade(&key_ptr));
        }
    }
}

impl<K, V> ExecuteMapCmd<K, V> for Tester<K, V>
where
    K: Clone + Debug + Eq + Hash + Ord,
    V: Debug,
{
    fn insert(&mut self, strategy: InsertStrategy, key: &K, value: &V, log: bool) {
        self.insert_impl(strategy, Arc::new(key.clone()), value, log);
    }

    fn reinsert(&mut self, strategy: InsertStrategy, index: usize, value: &V) {
        if let Some(key) = self.nth_key_mod_len(index) {
            self.insert_impl(strategy, key, value, false);
        }
    }

    fn remove_inserted(&mut self, strategy: RemoveStrategy, index: usize) {
        if let Some(key) = self.nth_key_mod_len(index) {
            let old_w = match strategy {
                RemoveStrategy::ViaRemove
                | RemoveStrategy::ViaRemoveEntry
                | RemoveStrategy::ViaEntry => self.weak.remove(&key),
                RemoveStrategy::ViaRetain => {
                    let mut removed: bool = false;
                    self.weak.retain(|k| {
                        if Arc::ptr_eq(&k, &key) {
                            removed = true;
                            false
                        } else {
                            true
                        }
                    });
                    removed
                }
                RemoveStrategy::ViaExtractIf => {
                    let removed: Vec<_> = self.weak.extract_if(|k| Arc::ptr_eq(&k, &key)).collect();
                    assert!(removed.len() <= 1);
                    !removed.is_empty()
                }
            };
            let old_s = self.strong.remove(&KeyByPtr(key));
            assert_eq!(old_s, old_w);
        }
    }

    fn remove_other(&mut self, _strategy: RemoveStrategy, _key: &K) {
        // There is no sensible implementation of this, since it needs to work
        // by value.
    }

    fn forget_inserted(&mut self, _: ForgetStrategy, index: usize) {
        if let Some(key) = self.nth_key_mod_len(index) {
            self.strong.remove(&KeyByPtr(key));
        }
    }

    fn reserve(&mut self, n: usize, try_reserve: bool) {
        if try_reserve {
            self.weak.try_reserve(n).expect("failed");
        } else {
            self.weak.reserve(n);
        }
    }

    fn shrink(&mut self, min_capacity: Option<usize>) {
        match min_capacity {
            Some(n) => self.weak.shrink_to(n),
            None => self.weak.shrink_to_fit(),
        }
    }

    fn clear(&mut self) {
        self.weak.clear();
        self.strong.clear();
    }
}
