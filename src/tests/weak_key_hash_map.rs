use crate as weak_table2;

use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::rc::{Rc, Weak};

use quickcheck::{quickcheck, Arbitrary, Gen};

use weak_table::WeakKeyHashMap;

use self::Cmd::*;

fn test_script<K, V>(script: &Script<K, V>) -> bool
where
    K: Clone + Debug + Eq + Hash + Ord,
    V: Clone + Debug + Eq + Ord,
{
    let mut tester = Tester::with_capacity(4);
    tester.execute_script(script);
    tester.check()
}

quickcheck! {
    fn prop_u8_u8(script: Script<u8, u8>) -> bool {
        test_script(&script)
    }

    fn prop_string_usize(script: Script<String, usize>) -> bool {
        test_script(&script)
    }
}

#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub enum InsertStrategy {
    ViaEntry,
    ViaInsert,
    ViaExtend,
}

#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub enum RemoveStrategy {
    ViaEntry,
    ViaRemove,
}

#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum Cmd<K, V> {
    Insert(InsertStrategy, K, V),
    Reinsert(InsertStrategy, usize, V),
    RemoveInserted(RemoveStrategy, usize),
    RemoveOther(RemoveStrategy, K),
    ForgetInserted(usize),
    Reserve(usize),
    ShrinkToFit,
    Clear,
}

#[derive(Clone, Debug)]
pub struct Script<K, V>(Vec<Cmd<K, V>>);

#[derive(Clone, Debug)]
pub struct Tester<K: Hash + Eq, V> {
    weak: WeakKeyHashMap<Weak<K>, V>,
    strong: HashMap<Rc<K>, V>,
    log: Vec<K>,
}

impl<K, V> Tester<K, V>
where
    K: Hash + Eq + Clone + Debug + Ord,
    V: Eq + Clone + Debug + Ord,
{
    pub fn with_capacity(capacity: usize) -> Self {
        Tester {
            weak: WeakKeyHashMap::with_capacity(capacity),
            strong: HashMap::new(),
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
            let weak2: WeakKeyHashMap<Weak<K>, V> = self
                .strong
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
            assert_eq!(&weak2, &self.weak);

            let weak3 = weak2.clone();
            assert_eq!(&weak3, &self.weak);
        }

        // Use index functionality to test for matches.
        {
            let mut weak2 = self.weak.clone();
            for (k, v) in self.strong.iter() {
                assert_eq!(&self.weak[k], v);
                assert_eq!(&mut weak2[k], v);
            }
        }
        // Use get functionality to test for matches.
        {
            for (k, v) in self.strong.iter() {
                assert_eq!(self.weak.get(k.as_ref()), Some(v));
                assert_eq!(self.weak.get_both(k.as_ref()), Some((k.clone(), v)));
            }
            let mut weak2: WeakKeyHashMap<Weak<K>, V> = self.weak.clone();
            for (k, v) in self.strong.clone().iter_mut() {
                assert_eq!(weak2.get_mut(k.as_ref()), Some(v));
            }
            for (k, v) in self.strong.clone().iter_mut() {
                assert_eq!(weak2.get_both_mut(k.as_ref()), Some((k.clone(), v)));
            }
        }

        // Use Entry functionality to test for matches.
        {
            let mut weak2 = self.weak.clone();
            for (k, v) in self.strong.iter() {
                let ent = weak2.entry(k.clone());
                assert_eq!(ent.key(), k);
                match ent {
                    weak_table2::weak_key_hash_map::Entry::Occupied(mut occ) => {
                        assert_eq!(occ.key(), k);
                        assert_eq!(occ.get(), v);
                        assert_eq!(occ.get_mut(), v);
                        assert_eq!(occ.into_mut(), v);
                    }
                    weak_table2::weak_key_hash_map::Entry::Vacant(_) => panic!("entry not present"),
                }
            }
        }

        // Check key and value iterators; make sure they match.
        {
            let mut k1: Vec<Rc<K>> = self.weak.keys().collect();
            let mut k2: Vec<Rc<K>> = self.strong.keys().cloned().collect();
            k1.sort();
            k2.sort();
            assert_eq!(k1, k2);

            let mut v1: Vec<V> = self.weak.values().cloned().collect();
            let mut v2: Vec<V> = self.strong.values().cloned().collect();
            v1.sort();
            v2.sort();
            assert_eq!(v1, v2);
        }

        // Check mutable iterators, make sure they match.
        {
            let mut weak2 = self.weak.clone();
            let mut v1: Vec<V> = weak2.values_mut().map(|v| v.clone()).collect();
            let mut v2: Vec<V> = self.strong.values().cloned().collect();
            v1.sort();
            v2.sort();
            assert_eq!(v1, v2);

            let mut e1: Vec<(Rc<K>, V)> = weak2
                .iter_mut()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
            let mut e2: Vec<(Rc<K>, V)> = self
                .strong
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
            e1.sort();
            e2.sort();
            assert_eq!(e1, e2);
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
        let copy = self.weak.iter().map(|(k, v)| (k, v.clone())).collect();
        if self.strong == copy {
            //            eprintln!("Tester::check: succeeded: {:?}", self.weak);
            true
        } else {
            eprintln!("Tester::check: failed: {:?} ≠ {:?}", self.strong, copy);
            false
        }
    }

    pub fn execute_script(&mut self, script: &Script<K, V>) {
        //        eprintln!("\n*** Starting script ***");
        for cmd in &script.0 {
            self.execute_command(cmd);
        }
    }

    pub fn execute_command(&mut self, cmd: &Cmd<K, V>) {
        //        eprintln!("Executing command: {:?}", cmd);
        match *cmd {
            Insert(strategy, ref k, ref v) => self.insert(strategy, k, v, true),
            Reinsert(strategy, index, ref v) => self.reinsert(strategy, index, v),
            RemoveInserted(strategy, index) => self.remove_inserted(strategy, index),
            RemoveOther(strategy, ref k) => self.remove_other(strategy, k),
            ForgetInserted(index) => self.forget_inserted(index),
            Reserve(n) => self.reserve(n),
            ShrinkToFit => self.shrink_to_fit(),
            Clear => self.clear(),
        }
        //        eprintln!("Table state: {:?}", self.weak);
    }

    pub fn insert(&mut self, strategy: InsertStrategy, key: &K, value: &V, log: bool) {
        let key_ptr = Rc::new(key.clone());
        match strategy {
            InsertStrategy::ViaEntry => {
                let ent = self.weak.entry(key_ptr.clone());
                assert_eq!(ent.key(), &key_ptr);
                match ent {
                    weak_table2::weak_key_hash_map::Entry::Occupied(mut occ) => {
                        assert_eq!(occ.key(), &key_ptr);
                        occ.insert(value.clone());
                    }
                    weak_table2::weak_key_hash_map::Entry::Vacant(vac) => {
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
        self.strong.remove(key);
        self.strong.insert(key_ptr, value.clone());
        if log {
            self.log.push(key.clone());
        }
    }

    pub fn reinsert(&mut self, strategy: InsertStrategy, index: usize, value: &V) {
        if let Some(key) = self.nth_key_mod_len(index) {
            self.insert(strategy, &key, value, false);
        }
    }

    pub fn remove_inserted(&mut self, strategy: RemoveStrategy, index: usize) {
        if let Some(key) = self.nth_key_mod_len(index) {
            self.remove_other(strategy, &key);
        }
    }

    pub fn remove_other(&mut self, strategy: RemoveStrategy, key: &K) {
        let old_w = match strategy {
            RemoveStrategy::ViaEntry => {
                let key_ptr = Rc::new(key.clone());
                let ent = self.weak.entry(key_ptr);
                match ent {
                    weak_table2::weak_key_hash_map::Entry::Occupied(occ) => Some(occ.remove()),
                    weak_table2::weak_key_hash_map::Entry::Vacant(_) => None,
                }
            }
            RemoveStrategy::ViaRemove => self.weak.remove(key),
        };
        let old_s = self.strong.remove(key);
        assert_eq!(old_s, old_w);
    }

    pub fn forget_inserted(&mut self, index: usize) {
        if let Some(key) = self.nth_key_mod_len(index) {
            self.strong.remove(&key);
        }
    }

    pub fn reserve(&mut self, n: usize) {
        self.weak.reserve(n);
    }

    pub fn shrink_to_fit(&mut self) {
        self.weak.shrink_to_fit();
    }
    pub fn clear(&mut self) {
        self.weak.clear();
        self.strong.clear();
    }

    fn nth_key_mod_len(&self, n: usize) -> Option<K> {
        if self.log.is_empty() {
            None
        } else {
            Some(self.log[n % self.log.len()].clone())
        }
    }
}

// TODO: consider migrating to something that uses arbitrary::Arbitrary, which
// has a derive macro.
impl<K: Arbitrary, V: Arbitrary> Arbitrary for Cmd<K, V> {
    fn arbitrary(g: &mut Gen) -> Self {
        let choice = u8::arbitrary(g);

        match choice % 13 {
            0..=3 => Insert(
                InsertStrategy::arbitrary(g),
                K::arbitrary(g),
                V::arbitrary(g),
            ),
            4 => Reinsert(
                InsertStrategy::arbitrary(g),
                usize::arbitrary(g),
                V::arbitrary(g),
            ),
            5..=6 => RemoveInserted(RemoveStrategy::arbitrary(g), usize::arbitrary(g)),
            7 => RemoveOther(RemoveStrategy::arbitrary(g), K::arbitrary(g)),
            8..=9 => ForgetInserted(usize::arbitrary(g)),
            10 => Reserve(usize::arbitrary(g) % 32),
            11 => ShrinkToFit,
            12 => Clear,
            _ => unreachable!(),
        }
    }
}

impl<K: Arbitrary, V: Arbitrary> Arbitrary for Script<K, V> {
    fn arbitrary(g: &mut Gen) -> Self {
        Script(Vec::<Cmd<K, V>>::arbitrary(g))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(self.0.shrink().map(|v| Script(v)))
    }
}

impl Arbitrary for InsertStrategy {
    fn arbitrary(g: &mut Gen) -> Self {
        let choice: u8 = u8::arbitrary(g);
        match choice % 3 {
            0 => InsertStrategy::ViaEntry,
            1 => InsertStrategy::ViaInsert,
            2 => InsertStrategy::ViaExtend,
            _ => unreachable!(),
        }
    }
}

impl Arbitrary for RemoveStrategy {
    fn arbitrary(g: &mut Gen) -> Self {
        let choice: u8 = u8::arbitrary(g);
        match choice % 2 {
            0 => RemoveStrategy::ViaEntry,
            1 => RemoveStrategy::ViaRemove,
            _ => unreachable!(),
        }
    }
}
