extern crate weak_table;

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
