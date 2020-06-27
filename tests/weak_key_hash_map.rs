use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::rc::{Rc, Weak};

use rand::Rng;
use quickcheck::{Arbitrary, Gen, quickcheck};

use weak_table::WeakKeyHashMap;

use self::Cmd::*;

fn test_script<K, V>(script: &Script<K, V>) -> bool
    where K: Clone + Debug + Eq + Hash,
          V: Clone + Debug + Eq
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

#[derive(Clone, Debug)]
pub enum Cmd<K, V>
{
    Insert(K, V),
    Reinsert(usize, V),
    RemoveInserted(usize),
    RemoveOther(K),
    ForgetInserted(usize),
}

#[derive(Clone, Debug)]
pub struct Script<K, V>(Vec<Cmd<K, V>>);

#[derive(Clone, Debug)]
pub struct Tester<K: Hash + Eq, V> {
    weak:   WeakKeyHashMap<Weak<K>, V>,
    strong: HashMap<Rc<K>, V>,
    log:    Vec<K>,
}

impl<K, V> Tester<K, V>
    where K: Hash + Eq + Clone + Debug,
          V: Eq + Clone + Debug
{
    pub fn new() -> Self {
        Tester::with_capacity(8)
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Tester {
            weak:   WeakKeyHashMap::with_capacity(capacity),
            strong: HashMap::new(),
            log:    Vec::new(),
        }
    }

    pub fn check(&self) -> bool {
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
            Insert(ref k, ref v)    => self.insert(k, v, true),
            Reinsert(index, ref v)  => self.reinsert(index, v),
            RemoveInserted(index)   => self.remove_inserted(index),
            RemoveOther(ref k)      => self.remove_other(k),
            ForgetInserted(index)   => self.forget_inserted(index),
        }
//        eprintln!("Table state: {:?}", self.weak);
    }

    pub fn insert(&mut self, key: &K, value: &V, log: bool) {
        let key_ptr = Rc::new(key.clone());
        self.weak.insert(key_ptr.clone(), value.clone());
        self.strong.remove(key);
        self.strong.insert(key_ptr, value.clone());
        if log { self.log.push(key.clone()); }
    }

    pub fn reinsert(&mut self, index: usize, value: &V) {
        if let Some(key) = self.nth_key_mod_len(index) {
            self.insert(&key, value, false);
        }
    }

    pub fn remove_inserted(&mut self, index: usize) {
        if let Some(key) = self.nth_key_mod_len(index) {
            self.strong.remove(&key);
            self.weak.remove(&key);
        }
    }

    pub fn remove_other(&mut self, key: &K) {
        self.strong.remove(key);
        self.weak.remove(key);
    }

    pub fn forget_inserted(&mut self, index: usize) {
        if let Some(key) = self.nth_key_mod_len(index) {
            self.strong.remove(&key);
        }
    }

    fn nth_key_mod_len(&self, n: usize) -> Option<K>
    {
        if self.log.is_empty() {
            None
        } else {
            Some(self.log[n % self.log.len()].clone())
        }
    }
}

impl<K: Arbitrary, V: Arbitrary> Arbitrary for Cmd<K, V> {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let choice = g.gen_range(0, 100);

        match choice {
            00..=39 => Insert(K::arbitrary(g), V::arbitrary(g)),
            40..=49 => Reinsert(usize::arbitrary(g), V::arbitrary(g)),
            50..=69 => RemoveInserted(usize::arbitrary(g)),
            70..=79 => RemoveOther(K::arbitrary(g)),
            80..=99 => ForgetInserted(usize::arbitrary(g)),
            _       => unreachable!(),
        }
    }
}

impl<K: Arbitrary, V: Arbitrary> Arbitrary for Script<K, V> {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        Script(Vec::<Cmd<K, V>>::arbitrary(g))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item=Self>> {
        Box::new(self.0.shrink().map(|v| Script(v)))
    }
}
