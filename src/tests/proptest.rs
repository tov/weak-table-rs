//! Property tests for the various map and set types.
//
// TODO: There is a lot of duplicate code in these modules; it would be neat to
// see about consolidating them into a more unified logic.
//
// TODO: Property tests are good at making sure that mucking around with containers
// preserves their associated invariants, but not so good at making
// sure that each operation actually handles its job correctly in all respects.
// They are not a substitute for unit tests, even though that's how we're using
// them here.

mod ptr_weak_hash_set;
mod ptr_weak_key_hash_map;
mod ptr_weak_weak_hash_map;
mod weak_hash_set;
mod weak_key_hash_map;
mod weak_value_hash_map;
mod weak_weak_hash_map;

use crate::compat::sync::Arc;
use crate::compat::*;
use core::cmp::Ordering;
use quickcheck::{Arbitrary, Gen};

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
    ViaRetain,
}

#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub enum ForgetStrategy {
    ForgetKey,
    ForgetValue,
    ForgetBoth,
}

#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum MapCmd<K, V> {
    Insert(InsertStrategy, K, V),
    Reinsert(InsertStrategy, usize, V),
    RemoveInserted(RemoveStrategy, usize),
    RemoveOther(RemoveStrategy, K),
    ForgetInserted(ForgetStrategy, usize),
    Reserve(usize, bool),
    ShrinkToFit(Option<usize>),
    Clear,
}

#[derive(Clone, Debug)]
pub struct MapScript<K, V>(Vec<MapCmd<K, V>>);

// TODO: consider migrating to something that uses arbitrary::Arbitrary, which
// has a derive macro.
impl<K: Arbitrary, V: Arbitrary> Arbitrary for MapCmd<K, V> {
    fn arbitrary(g: &mut Gen) -> Self {
        use MapCmd::*;
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
            8..=9 => ForgetInserted(ForgetStrategy::arbitrary(g), usize::arbitrary(g)),
            10 => Reserve(usize::arbitrary(g) % 32, bool::arbitrary(g)),
            11 => ShrinkToFit(if bool::arbitrary(g) {
                Some(usize::arbitrary(g) % 32)
            } else {
                None
            }),
            12 => Clear,
            _ => unreachable!(),
        }
    }
}

impl<K: Arbitrary, V: Arbitrary> Arbitrary for MapScript<K, V> {
    fn arbitrary(g: &mut Gen) -> Self {
        MapScript(Vec::<MapCmd<K, V>>::arbitrary(g))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(self.0.shrink().map(|v| MapScript(v)))
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
        match choice % 3 {
            0 => RemoveStrategy::ViaEntry,
            1 => RemoveStrategy::ViaRemove,
            2 => RemoveStrategy::ViaRetain,
            _ => unreachable!(),
        }
    }
}

impl Arbitrary for ForgetStrategy {
    fn arbitrary(g: &mut Gen) -> Self {
        let choice: u8 = u8::arbitrary(g);
        match choice % 3 {
            0 => ForgetStrategy::ForgetKey,
            1 => ForgetStrategy::ForgetValue,
            2 => ForgetStrategy::ForgetBoth,
            _ => unreachable!(),
        }
    }
}

trait ExecuteMapCmd<K, V>: Debug {
    fn execute_command(&mut self, cmd: &MapCmd<K, V>) {
        use MapCmd::*;
        match *cmd {
            Insert(strategy, ref k, ref v) => self.insert(strategy, k, v, true),
            Reinsert(strategy, index, ref v) => self.reinsert(strategy, index, v),
            RemoveInserted(strategy, index) => self.remove_inserted(strategy, index),
            RemoveOther(strategy, ref k) => self.remove_other(strategy, k),
            ForgetInserted(strategy, index) => self.forget_inserted(strategy, index),
            Reserve(n, try_reserve) => self.reserve(n, try_reserve),
            ShrinkToFit(min_capacity) => self.shrink(min_capacity),
            Clear => self.clear(),
        }
    }

    fn execute_script(&mut self, script: &MapScript<K, V>) {
        //        eprintln!("\n*** Starting script ***");
        for cmd in &script.0 {
            self.execute_command(cmd);
        }
    }

    fn insert(&mut self, strategy: InsertStrategy, key: &K, value: &V, log: bool);

    fn reinsert(&mut self, strategy: InsertStrategy, index: usize, value: &V);

    fn remove_inserted(&mut self, strategy: RemoveStrategy, index: usize);

    fn remove_other(&mut self, strategy: RemoveStrategy, key: &K);

    fn forget_inserted(&mut self, strategy: ForgetStrategy, index: usize);

    fn reserve(&mut self, n: usize, try_reserve: bool);

    fn shrink(&mut self, min_capacity: Option<usize>);

    fn clear(&mut self);
}

// Wrapper to allow using Arc<K> as a by-pointer key of a _strong_ hashmap or hashset.
#[derive(Clone, Debug)]
struct KeyByPtr<K>(sync::Arc<K>);

impl<K> PartialEq for KeyByPtr<K> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl<K> Eq for KeyByPtr<K> {}
impl<K> Hash for KeyByPtr<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let ptr = Arc::as_ptr(&self.0) as *const ();
        ptr.hash(state);
    }
}
impl<K> PartialOrd for KeyByPtr<K> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl<K> Ord for KeyByPtr<K> {
    fn cmp(&self, other: &Self) -> Ordering {
        let p1 = Arc::as_ptr(&self.0) as *const ();
        let p2 = Arc::as_ptr(&other.0) as *const ();
        p1.cmp(&p2)
    }
}
