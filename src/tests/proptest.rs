//!  Property tests for the various map and set types.
mod weak_key_hash_map;

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

// TODO: consider migrating to something that uses arbitrary::Arbitrary, which
// has a derive macro.
impl<K: Arbitrary, V: Arbitrary> Arbitrary for Cmd<K, V> {
    fn arbitrary(g: &mut Gen) -> Self {
        use Cmd::*;
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
