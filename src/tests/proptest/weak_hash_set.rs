use crate as weak_table2;

use core::marker::PhantomData;

use crate::compat::{
    rc::{Rc, Weak},
    *,
};
use quickcheck::quickcheck;

use weak_table2::WeakHashSet;

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
    weak: WeakHashSet<Weak<K>>,
    strong: HashSet<Rc<K>>,
    log: Vec<K>,

    _phantom: PhantomData<V>,
}

impl<K, V> Tester<K, V>
where
    K: Hash + Eq + Clone + Debug + Ord,
{
    pub fn with_capacity(capacity: usize) -> Self {
        Tester {
            weak: WeakHashSet::with_capacity(capacity),
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
            let weak2: WeakHashSet<Weak<K>> = self.strong.iter().cloned().collect();
            assert_eq!(&weak2, &self.weak);

            let weak3 = weak2.clone();
            assert_eq!(&weak3, &self.weak);
        }

        // Use contains functionality to test for matches.
        {
            for k in self.weak.iter() {
                assert!(self.strong.contains(k.as_ref()));
            }
            for k in self.strong.iter() {
                assert!(self.weak.contains(k.as_ref()));
            }
        }
        // Use a few other iterator types to construct a version of the strong
        // table.
        {
            let weak2 = self.weak.clone();
            let copy: HashSet<_> = weak2.into_iter().collect();
            assert_eq!(copy, self.strong);

            let mut weak3 = self.weak.clone();
            let copy: HashSet<_> = weak3.drain().collect();
            assert_eq!(copy, self.strong);
            assert!(weak3.is_empty());
        }

        // Construct version of strong table, make sure it is the same.
        let copy = self.weak.iter().collect();
        if self.strong == copy {
            //            eprintln!("Tester::check: succeeded: {:?}", self.weak);
            true
        } else {
            eprintln!("Tester::check: failed: {:?} ≠ {:?}", self.strong, copy);
            false
        }
    }

    fn nth_key_mod_len(&self, n: usize) -> Option<K> {
        if self.log.is_empty() {
            None
        } else {
            Some(self.log[n % self.log.len()].clone())
        }
    }
}

impl<K, V> ExecuteMapCmd<K, V> for Tester<K, V>
where
    K: Clone + Debug + Eq + Hash + Ord,
    V: Debug,
{
    fn insert(&mut self, strategy: InsertStrategy, key: &K, _value: &V, log: bool) {
        let key_ptr = Rc::new(key.clone());
        match strategy {
            InsertStrategy::ViaEntry | InsertStrategy::ViaInsert => {
                let _ = self.weak.insert(key_ptr.clone());
            }
            InsertStrategy::ViaExtend => {
                let lst = [key_ptr.clone()];
                self.weak.extend(lst);
            }
        }
        self.strong.remove(key);
        self.strong.insert(key_ptr);
        if log {
            self.log.push(key.clone());
        }
    }

    fn reinsert(&mut self, strategy: InsertStrategy, index: usize, value: &V) {
        if let Some(key) = self.nth_key_mod_len(index) {
            self.insert(strategy, &key, value, false);
        }
    }

    fn remove_inserted(&mut self, strategy: RemoveStrategy, index: usize) {
        if let Some(key) = self.nth_key_mod_len(index) {
            self.remove_other(strategy, &key);
        }
    }

    fn remove_other(&mut self, _strategy: RemoveStrategy, key: &K) {
        let old_w = self.weak.remove(key);
        let old_s = self.strong.remove(key);
        assert_eq!(old_s, old_w);
    }

    fn forget_inserted(&mut self, _: ForgetStrategy, index: usize) {
        if let Some(key) = self.nth_key_mod_len(index) {
            self.strong.remove(&key);
        }
    }

    fn reserve(&mut self, n: usize) {
        self.weak.reserve(n);
    }

    fn shrink_to_fit(&mut self) {
        self.weak.shrink_to_fit();
    }
    fn clear(&mut self) {
        self.weak.clear();
        self.strong.clear();
    }
}
