extern crate weak_table;

use weak_table::WeakHashSet;

use std::rc::{Rc, Weak};

#[derive(Clone, Debug)]
pub struct Symbol {
    name: Rc<str>,
}

#[derive(Debug, Default)]
pub struct SymbolTable {
    table: WeakHashSet<Weak<str>>,
}

impl PartialEq for Symbol {
    fn eq(&self, other: &Symbol) -> bool {
        self.name.as_ptr() == other.name.as_ptr()
    }
}

impl Eq for Symbol {}

impl Symbol {
    pub fn uninterned(name: &str) -> Self {
        Symbol {
            name: Rc::from(name),
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}

impl SymbolTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern(&mut self, name: &str) -> Symbol {
        let rc = if let Some(symbol) = self.table.get(name) {
            symbol
        } else {
            let result = Rc::<str>::from(name);
            self.table.insert(result.clone());
            result
        };

        Symbol {
            name: rc,
        }
    }
}

#[test]
fn symbols() {
    let mut tab = SymbolTable::new();

    let a0 = tab.intern("a");
    let a1 = tab.intern("a");
    let a2 = Symbol::uninterned("a");
    let b  = tab.intern("b");

    assert_eq!(a0, a1);
    assert_ne!(a0, a2);
    assert_ne!(a1, a2);
    assert_ne!(a0, b);

    assert_eq!(a0.name(), "a");
    assert_eq!(a1.name(), "a");
    assert_eq!(a2.name(), "a");
    assert_eq!(b.name(),  "b");
}
