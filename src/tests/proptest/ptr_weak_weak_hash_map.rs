use crate as weak_table2;

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::{Arc, Weak};

use quickcheck::quickcheck;

use weak_table2::ptr_weak_weak_hash_map::Entry;
use weak_table2::PtrWeakWeakHashMap;

use super::{ExecuteMapCmd, ForgetStrategy, InsertStrategy, KeyByPtr, MapScript, RemoveStrategy};

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
    weak: PtrWeakWeakHashMap<Weak<K>, Weak<V>>,
    strong: HashMap<KeyByPtr<K>, Arc<V>>,
    log: Vec<Weak<K>>,

    // objects that we are retaining only to keep them alive.
    retain_keys: HashSet<KeyByPtr<K>>,
    retain_values: HashSet<KeyByPtr<V>>,
}

impl<K, V> Tester<K, V>
where
    K: Hash + Eq + Clone + Debug + Ord,
    V: Eq + Clone + Debug + Ord,
{
    pub fn with_capacity(capacity: usize) -> Self {
        Tester {
            weak: PtrWeakWeakHashMap::with_capacity(capacity),
            strong: HashMap::new(),
            log: Vec::new(),
            retain_keys: HashSet::new(),
            retain_values: HashSet::new(),
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
            let weak2: PtrWeakWeakHashMap<Weak<K>, Weak<V>> = self
                .strong
                .iter()
                .map(|(k, v)| (k.0.clone(), v.clone()))
                .collect();
            assert_eq!(&weak2, &self.weak);

            let weak3 = weak2.clone();
            assert_eq!(&weak3, &self.weak);
        }

        // Use get functionality to test for matches.
        {
            for (k, v) in self.strong.iter() {
                assert_eq!(self.weak.get(&k.0), Some(v.clone()));
            }
        }

        // Use Entry functionality to test for matches.
        {
            let mut weak2 = self.weak.clone();
            for (k, v) in self.strong.iter() {
                let ent = weak2.entry(k.0.clone());
                assert_eq!(ent.key(), &k.0);
                match ent {
                    Entry::Occupied(occ) => {
                        assert_eq!(occ.key(), &k.0);
                        assert_eq!(occ.get(), v);
                        assert_eq!(occ.get_strong(), v.clone());
                    }
                    Entry::Vacant(_) => panic!("entry not present"),
                }
            }
        }

        // Check key and value iterators; make sure they match.
        {
            let mut k1: Vec<KeyByPtr<K>> = self.weak.keys().map(KeyByPtr).collect();
            let mut k2: Vec<KeyByPtr<K>> = self.strong.keys().cloned().collect();
            k1.sort();
            k2.sort();
            assert_eq!(k1, k2);

            let mut v1: Vec<Arc<V>> = self.weak.values().collect();
            let mut v2: Vec<Arc<V>> = self.strong.values().cloned().collect();
            v1.sort();
            v2.sort();
            assert_eq!(v1, v2);
        }

        // Use a few other iterator types to construct a version of the strong
        // table.
        {
            let weak2 = self.weak.clone();
            let copy: HashMap<_, _> = weak2.into_iter().map(|(k, v)| (KeyByPtr(k), v)).collect();
            assert_eq!(copy, self.strong);

            let mut weak3 = self.weak.clone();
            let copy: HashMap<_, _> = weak3.drain().map(|(k, v)| (KeyByPtr(k), v)).collect();
            assert_eq!(copy, self.strong);
            assert!(weak3.is_empty());
        }

        // Construct version of strong table, make sure it is the same.
        let copy = self
            .weak
            .iter()
            .map(|(k, v)| (KeyByPtr(k), v.clone()))
            .collect();
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
    fn insert_impl(&mut self, strategy: InsertStrategy, key_ptr: Arc<K>, value: Arc<V>, log: bool) {
        match strategy {
            InsertStrategy::ViaEntry => {
                let ent = self.weak.entry(key_ptr.clone());
                assert_eq!(ent.key(), &key_ptr);
                match ent {
                    Entry::Occupied(mut occ) => {
                        assert_eq!(occ.key(), &key_ptr);
                        occ.insert(value.clone());
                    }
                    Entry::Vacant(vac) => {
                        assert_eq!(vac.key(), &key_ptr);
                        vac.insert(value.clone());
                    }
                }
            }
            InsertStrategy::ViaInsert => {
                let _ = self.weak.insert(key_ptr.clone(), value.clone());
            }
            InsertStrategy::ViaExtend => {
                let lst = [(key_ptr.clone(), value.clone())];
                self.weak.extend(lst);
            }
        }
        let strong_key = KeyByPtr(key_ptr.clone());
        self.strong.remove(&strong_key);
        self.strong.insert(strong_key, value.clone());
        if log {
            self.log.push(Arc::downgrade(&key_ptr));
        }
    }
}

impl<K, V> ExecuteMapCmd<K, V> for Tester<K, V>
where
    K: Clone + Debug + Eq + Hash + Ord,
    V: Clone + Debug + Eq + Ord,
{
    fn insert(&mut self, strategy: InsertStrategy, key: &K, value: &V, log: bool) {
        self.insert_impl(
            strategy,
            Arc::new(key.clone()),
            Arc::new(value.clone()),
            log,
        );
    }

    fn reinsert(&mut self, strategy: InsertStrategy, index: usize, value: &V) {
        if let Some(key) = self.nth_key_mod_len(index) {
            self.insert_impl(strategy, key, Arc::new(value.clone()), false);
        }
    }

    fn remove_inserted(&mut self, strategy: RemoveStrategy, index: usize) {
        if let Some(key) = self.nth_key_mod_len(index) {
            let old_w = match strategy {
                RemoveStrategy::ViaEntry => {
                    let ent = self.weak.entry(key.clone());
                    match ent {
                        Entry::Occupied(occ) => Some(occ.remove()),
                        Entry::Vacant(_) => None,
                    }
                }
                RemoveStrategy::ViaRemove => self.weak.remove(&key),
            };
            let old_s = self.strong.remove(&KeyByPtr(key.clone()));
            assert_eq!(old_s, old_w);
        }
    }

    fn remove_other(&mut self, _strategy: RemoveStrategy, _key: &K) {
        // This can't do anything meaningful: we need a copy of an inserted key
        // in order to remove that key.
    }

    fn forget_inserted(&mut self, strategy: ForgetStrategy, index: usize) {
        if let Some(key) = self.nth_key_mod_len(index) {
            if let Some((k, v)) = self.strong.remove_entry(&KeyByPtr(key)) {
                match strategy {
                    ForgetStrategy::ForgetKey => {
                        self.retain_keys.remove(&k);
                        drop(k);
                        self.retain_values.insert(KeyByPtr(v));
                    }
                    ForgetStrategy::ForgetValue => {
                        self.retain_values.remove(&KeyByPtr(v.clone()));
                        drop(v);
                        self.retain_keys.insert(k);
                    }
                    ForgetStrategy::ForgetBoth => {
                        self.retain_keys.remove(&k);
                        self.retain_values.remove(&KeyByPtr(v.clone()));
                        drop(k);
                        drop(v);
                    }
                }
            }
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
