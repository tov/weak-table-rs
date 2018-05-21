# weak-table-rs: weak hash maps and sets for Rust

[![Build Status](https://travis-ci.org/tov/weak-table-rs.svg?branch=master)](https://travis-ci.org/tov/weak-table-rs)
[![Crates.io](https://img.shields.io/crates/v/weak-table.svg?maxAge=2592000)](https://crates.io/crates/weak-table)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE-MIT)

This crate defines several kinds of weak hash maps and sets. See 
the [full API documentation](https://tov.github.io/weak-table-rs/).

## Usage

It’s [on crates.io](https://crates.io/crates/weak-table),
so you can add

```toml
[dependencies]
weak-table = "0.1.2"
```

to your `Cargo.toml` and

```rust
extern crate weak_table;
```

to your crate root.

### Examples

Here we create a weak hash set and demonstrate that it forgets elements
whose reference counts expire:

```rust
use weak_table::WeakHashSet;
use std::sync::{Arc, Weak};

type Table = WeakHashSet<Weak<str>>;

let mut set = Table::new();
let a = Arc::<str>::from("a");
let b = Arc::<str>::from("b");

set.insert(a.clone());

assert!(   set.contains("a") );
assert!( ! set.contains("b") );

set.insert(b.clone());

assert!(   set.contains("a") );
assert!(   set.contains("b") );

drop(a);

assert!( ! set.contains("a") );
assert!(   set.contains("b") );
```
