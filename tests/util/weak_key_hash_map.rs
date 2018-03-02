use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::rc::{Rc, Weak};

use quickcheck::{Arbitrary, Gen};

use weak_table::WeakKeyHashMap;

use super::rc_key::RcKey;
use self::Cmd::*;

#[derive(Clone, Debug)]
pub enum Cmd<K, V>
{
    Insert(K, V),
    RemoveInserted(usize),
    RemoveOther(K),
    ForgetInserted(usize),
}

#[derive(Clone, Debug)]
pub struct Script<K, V> {
    cmds: Vec<Cmd<K, V>>,
}

#[derive(Clone, Debug)]
pub struct Tester<K: Hash + Eq, V> {
    weak:   WeakKeyHashMap<Weak<K>, V>,
    strong: HashMap<RcKey<K>, V>,
    log:    Vec<K>,
}

impl<K, V> Tester<K, V>
    where K: Hash + Eq + Clone + Debug,
          V: Eq + Clone + Debug
{
    pub fn new() -> Self {
        Tester {
            weak:   WeakKeyHashMap::new(),
            strong: HashMap::new(),
            log:    Vec::new(),
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

    pub fn execute_command(&mut self, cmd: &Cmd<K, V>) {
        match *cmd {
            Insert(ref k, ref v) => {
                let kptr = Rc::new(k.clone());
                self.strong.insert(RcKey(kptr.clone()), v.clone());
                self.weak.insert(kptr, v.clone());
                self.log.push(k.clone());
            }
            RemoveInserted(index) => {
                if let Some(k) = self.nth_key_mod_len(index) {
                    self.strong.remove(&k);
                    self.weak.remove(&k);
                }
            }
            RemoveOther(ref k) => {
                self.strong.remove(k);
                self.weak.remove(k);
            }
            ForgetInserted(index) => {
                if let Some(k) = self.nth_key_mod_len(index) {
                    self.strong.remove(&k);
                }
            }
        }
    }

    pub fn execute_script(&mut self, script: &Script<K, V>) {
        for cmd in &script.cmds {
            self.execute_command(cmd);
        }
    }

    pub fn check(&self) -> bool {
        let copy = self.weak.iter().map(|(k, v)| (RcKey(k), v.clone())).collect();
        self.strong == copy
    }
}

impl<K: Arbitrary, V: Arbitrary> Arbitrary for Cmd<K, V> {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        let choice = g.gen_range(0, 100);

        match choice {
            00...49 => Insert(K::arbitrary(g), V::arbitrary(g)),
            50...69 => RemoveInserted(usize::arbitrary(g)),
            70...79 => RemoveOther(K::arbitrary(g)),
            80...99 => ForgetInserted(usize::arbitrary(g)),
            _       => unreachable!(),
        }
    }
}

impl<K: Arbitrary, V: Arbitrary> Arbitrary for Script<K, V> {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        Script {
            cmds: Vec::<Cmd<K, V>>::arbitrary(g)
        }
    }

    fn shrink(&self) -> Box<Iterator<Item=Self>> {
        Box::new(self.cmds.shrink().map(|v| Script { cmds: v }))
    }
}
