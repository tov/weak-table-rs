//!  Property tests for the various map and set types.
mod weak_key_hash_map;
mod weak_value_hash_map;
mod weak_weak_hash_map;

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
    Reserve(usize),
    ShrinkToFit,
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
            10 => Reserve(usize::arbitrary(g) % 32),
            11 => ShrinkToFit,
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
        match choice % 2 {
            0 => RemoveStrategy::ViaEntry,
            1 => RemoveStrategy::ViaRemove,
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

trait ExecuteMapCmd<K, V> {
    fn execute_command(&mut self, cmd: &MapCmd<K, V>) {
        use MapCmd::*;
        match *cmd {
            Insert(strategy, ref k, ref v) => self.insert(strategy, k, v, true),
            Reinsert(strategy, index, ref v) => self.reinsert(strategy, index, v),
            RemoveInserted(strategy, index) => self.remove_inserted(strategy, index),
            RemoveOther(strategy, ref k) => self.remove_other(strategy, k),
            ForgetInserted(strategy, index) => self.forget_inserted(strategy, index),
            Reserve(n) => self.reserve(n),
            ShrinkToFit => self.shrink_to_fit(),
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

    fn reserve(&mut self, n: usize);

    fn shrink_to_fit(&mut self);

    fn clear(&mut self);
}
