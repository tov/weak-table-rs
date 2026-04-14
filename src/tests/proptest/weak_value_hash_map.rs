use crate as weak_table2;

use crate::compat::{
    rc::{Rc, Weak},
    *,
};

use quickcheck::quickcheck;

use weak_table2::weak_value_hash_map::Entry;
use weak_table2::WeakValueHashMap;

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
    weak: WeakValueHashMap<K, Weak<V>>,
    strong: HashMap<K, Rc<V>>,
    log: Vec<K>,
}

impl<K, V> Tester<K, V>
where
    K: Hash + Eq + Clone + Debug + Ord,
    V: Eq + Clone + Debug + Ord,
{
    pub fn with_capacity(capacity: usize) -> Self {
        Tester {
            weak: WeakValueHashMap::with_capacity(capacity),
            strong: HashMap::default(),
            log: Vec::new(),
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
            let weak2: WeakValueHashMap<K, Weak<V>> = self
                .strong
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
            assert_eq!(&weak2, &self.weak);

            let weak3 = weak2.clone();
            assert_eq!(&weak3, &self.weak);
        }

        // Use get functionality to test for matches.
        {
            for (k, v) in self.strong.iter() {
                assert_eq!(self.weak.get(k), Some(v.clone()));
                assert!(self.weak.contains_key(k));
            }
        }

        // Use Entry functionality to test for matches.
        {
            let mut weak2 = self.weak.clone();
            for (k, v) in self.strong.iter() {
                let ent = weak2.entry(k.clone());
                assert_eq!(ent.key(), k);
                match ent {
                    Entry::Occupied(occ) => {
                        assert_eq!(occ.key(), k);
                        assert_eq!(occ.get(), v);
                        assert_eq!(occ.get_strong(), v.clone());
                    }
                    Entry::Vacant(_) => {
                        panic!("entry not present")
                    }
                }
            }
        }

        // Check key and value iterators; make sure they match.
        {
            let mut k1: Vec<K> = self.weak.keys().cloned().collect();
            let mut k2: Vec<K> = self.strong.keys().cloned().collect();
            k1.sort();
            k2.sort();
            assert_eq!(k1, k2);

            let mut v1: Vec<Rc<V>> = self.weak.values().collect();
            let mut v2: Vec<Rc<V>> = self.strong.values().cloned().collect();
            v1.sort();
            v2.sort();
            assert_eq!(v1, v2);
        }

        // Check into_keys and into_values iterators; make sure they match.
        {
            let mut k1: Vec<_> = self.weak.clone().into_keys().collect();
            let mut k2: Vec<_> = self.strong.clone().into_keys().collect();
            k1.sort();
            k2.sort();
            assert_eq!(k1, k2);

            let mut v1: Vec<_> = self.weak.clone().into_values().collect();
            let mut v2: Vec<_> = self.strong.clone().into_values().collect();
            v1.sort();
            v2.sort();
            assert_eq!(v1, v2);
        }

        // Use a few other iterator types to construct a version of the strong
        // table.
        {
            let weak2 = self.weak.clone();
            let copy: HashMap<_, _> = weak2.into_iter().collect();
            assert_eq!(copy, self.strong);

            let mut weak3 = self.weak.clone();
            let copy: HashMap<_, _> = weak3.drain().collect();
            assert_eq!(copy, self.strong);
            assert!(weak3.is_empty());
        }

        // Construct version of strong table, make sure it is the same.
        let copy = self.weak.iter().map(|(k, v)| (k.clone(), v)).collect();
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
    V: Clone + Debug + Eq + Ord,
{
    fn insert(&mut self, strategy: InsertStrategy, key: &K, value: &V, log: bool) {
        let val_ptr = Rc::new(value.clone());
        match strategy {
            InsertStrategy::ViaEntry => {
                let ent = self.weak.entry(key.clone());
                assert_eq!(ent.key(), key);
                match ent {
                    Entry::Occupied(mut occ) => {
                        assert_eq!(occ.key(), key);
                        occ.insert(val_ptr.clone());
                    }
                    Entry::Vacant(vac) => {
                        assert_eq!(vac.key(), key);
                        vac.insert(val_ptr.clone());
                    }
                }
            }
            InsertStrategy::ViaInsert => {
                let _ = self.weak.insert(key.clone(), val_ptr.clone());
            }
            InsertStrategy::ViaExtend => {
                let lst = [(key.clone(), val_ptr.clone())];
                self.weak.extend(lst);
            }
            InsertStrategy::ViaExtendRef => {
                let lst = [(key, &val_ptr)];
                self.weak.extend(lst);
            }
        }
        self.strong.remove(key);
        self.strong.insert(key.clone(), val_ptr.clone());
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

    fn remove_other(&mut self, strategy: RemoveStrategy, key: &K) {
        let old_w = match strategy {
            RemoveStrategy::ViaEntry => {
                let ent = self.weak.entry(key.clone());
                match ent {
                    Entry::Occupied(occ) => Some(occ.remove()),
                    Entry::Vacant(_) => None,
                }
            }
            RemoveStrategy::ViaRemove => self.weak.remove(key),
            RemoveStrategy::ViaRemoveEntry => self.weak.remove_entry(key).map(|(k, v)| {
                assert_eq!(&k, key);
                v
            }),
            RemoveStrategy::ViaRetain => {
                let mut removed = None;
                self.weak.retain(|k, v| {
                    if k == key {
                        removed = Some(v.clone());
                        false
                    } else {
                        true
                    }
                });
                removed
            }
            RemoveStrategy::ViaExtractIf => {
                let removed: Vec<_> = self.weak.extract_if(|k, _| k == key).collect();
                assert!(removed.len() <= 1);
                removed.get(0).map(|(_, v)| v.clone())
            }
        };
        let old_s = self.strong.remove(key);
        assert_eq!(old_s, old_w);
    }

    fn forget_inserted(&mut self, _: ForgetStrategy, index: usize) {
        if let Some(key) = self.nth_key_mod_len(index) {
            self.strong.remove(&key);
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
