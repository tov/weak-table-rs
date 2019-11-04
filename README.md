# weak-table: weak hash maps and sets for Rust

[![Build Status](https://travis-ci.org/tov/weak-table-rs.svg?branch=master)](https://travis-ci.org/tov/weak-table-rs)
[![Crates.io](https://img.shields.io/crates/v/weak-table.svg?maxAge=2592000)](https://crates.io/crates/weak-table)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE-MIT)

This crate defines several kinds of weak hash maps and sets. See 
the [full API documentation](http://docs.rs/weak-table/) for details.

This crate supports Rust version 1.32 and later.

### Examples

Here we create a weak hash map and demonstrate that it forgets mappings
whose keys expire:

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

#[test]
fn interning() {
    let mut tab = SymbolTable::new();

    let a0 = tab.intern("a");
    let a1 = tab.intern("a");
    let b  = tab.intern("b");

    assert_eq!(a0, a1);
    assert_ne!(a0, b);
}
```

