# weak-table: weak hash maps and sets for Rust

[![Build Status](https://github.com/tov/weak-table-rs/actions/workflows/ci.yml/badge.svg)](https://github.com/tov/weak-table-rs/actions)
[![Crates.io](https://img.shields.io/crates/v/weak-table.svg?maxAge=2592000)](https://crates.io/crates/weak-table)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE-MIT)

This crate defines several kinds of weak hash maps and sets.

- For a hash map where the keys are held by weak pointers and compared by key value, see
  [`WeakKeyHashMap`](struct.WeakKeyHashMap.html).
- For a hash map where the keys are held by weak pointers and compared by pointer, see
  [`PtrWeakKeyHashMap`](struct.PtrWeakKeyHashMap.html).
- For a hash map where the values are held by weak pointers, see
  [`WeakValueHashMap`](struct.WeakValueHashMap.html).
- For a hash map where the keys and values are both held by weak pointers and the keys are
  compared by value, see
  [`WeakWeakHashMap`](struct.WeakWeakHashMap.html).
- For a hash map where the keys and values are both held by weak pointers and the keys are
  compared by pointer, see
  [`PtrWeakWeakHashMap`](struct.PtrWeakWeakHashMap.html).
- For a hash set where the elements are held by weak pointers and compared by element value, see
  [`WeakHashSet`](struct.WeakHashSet.html).

- For a hash set where the elements are held by weak pointers and compared by pointer, see
  [`PtrWeakHashSet`](struct.PtrWeakHashSet.html).

To add support for your own weak pointers, see
[the traits `WeakElement` and `WeakKey`](traits/).

### Rust version support

This crate supports Rust version 1.46 and later.

### Crate features

`weak-table` is built with the `std` feature, which enables
functionality dependent on the `std` library, enabled by default.
Optionally, the following dependency may be enabled:

  - `ahash`: use `ahash`’s hasher rather than the `std` hasher

If the `std` feature is disabled (for no_std) then the `ahash` dependency **must** be enabled.


### Asymptotic complexity


Most operations have documented asymptotic time complexities. When time complexities are
given in big-*O* notation, the following parameters are used consistently:

- *n*: the *capacity* of the map or set being accessed or constructed
- *m*: the *capacity* of a second map/set involved in a submap/subset operation
- *p*: the length of the probe sequence for the key in question

Note that *p* ∈ *O*(*n*), but we expect it to be *O*(1).

### Examples

Here we create a weak hash table mapping strings to integers.
Note that after dropping `one`, the key `"one"` is no longer present in the map.
This is because the map holds the strings as `std::sync::Weak<str>`s.

```rust
use weak_table::WeakKeyHashMap;
use std::sync::{Arc, Weak};

let mut table = <WeakKeyHashMap<Weak<str>, u32>>::new();
let one = Arc::<str>::from("one");
let two = Arc::<str>::from("two");

table.insert(one.clone(), 1);

assert_eq!( table.get("one"), Some(&1) );
assert_eq!( table.get("two"), None );

table.insert(two.clone(), 2);
*table.get_mut(&one).unwrap() += 10;

assert_eq!( table.get("one"), Some(&11) );
assert_eq!( table.get("two"), Some(&2) );

drop(one);

assert_eq!( table.get("one"), None );
assert_eq!( table.get("two"), Some(&2) );
```

Here we use a weak hash set to implement a simple string interning facility:

```rust
use weak_table::WeakHashSet;
use std::ops::Deref;
use std::rc::{Rc, Weak};

#[derive(Clone, Debug)]
pub struct Symbol(Rc<str>);

impl PartialEq for Symbol {
    fn eq(&self, other: &Symbol) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Symbol {}

impl Deref for Symbol {
    type Target = str;
    fn deref(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, Default)]
pub struct SymbolTable(WeakHashSet<Weak<str>>);

impl SymbolTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern(&mut self, name: &str) -> Symbol {
        if let Some(rc) = self.0.get(name) {
            Symbol(rc)
        } else {
            let rc = Rc::<str>::from(name);
            self.0.insert(Rc::clone(&rc));
            Symbol(rc)
        }
    }
}

fn interning_test() {
    let mut tab = SymbolTable::new();

    let a0 = tab.intern("a");
    let a1 = tab.intern("a");
    let b  = tab.intern("b");

    assert_eq!(a0, a1);
    assert_ne!(a0, b);
}
# interning_test();
```

