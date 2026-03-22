#![allow(dead_code)]

mod table;
mod wrappers;

pub(crate) use table::*;
pub(crate) use wrappers::*;

pub(crate) type WeakK<T> = Weak<T, u64>;
pub(crate) type WeakV<T> = Weak<T, ()>;
