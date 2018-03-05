//! # weak-table-rs: weak hash maps and sets for Rust
//!
//!   - For a hash set where the elements are held by weak pointers and compared by element value, see
//!     [`WeakHashSet`](weak_hash_set/struct.WeakHashSet.html).
//!
//!   - For a hash set where the elements are held by weak pointers and compared by pointer, see
//!     [`PtrWeakHashSet`](ptr_weak_hash_set/struct.PtrWeakHashSet.html).
//!
//!   - For a hash map where the keys are held by weak pointers and compared by key value, see
//!     [`WeakKeyHashMap`](weak_key_hash_map/struct.WeakKeyHashMap.html).
//!
//!   - For a hash map where the keys are held by weak pointers and compared by pointer, see
//!     [`PtrWeakKeyHashMap`](ptr_weak_key_hash_map/struct.PtrWeakKeyHashMap.html).
//!
//!   - For a hash map where the values are held by weak pointers, see
//!     [`WeakValueHashMap`](weak_value_hash_map/struct.WeakValueHashMap.html).
//!
//! # Examples
//!
//! ```
//! use weak_table::WeakHashSet;
//! use std::sync::{Arc, Weak};
//!
//! type Table = WeakHashSet<Weak<String>>;
//!
//! let mut set = Table::new();
//! let a = Arc::new("a".to_string());
//! let b = Arc::new("b".to_string());
//!
//! set.insert(a.clone());
//!
//! assert!(   set.contains("a") );
//! assert!( ! set.contains("b") );
//!
//! set.insert(b.clone());
//!
//! assert!(   set.contains("a") );
//! assert!(   set.contains("b") );
//!
//! drop(a);
//!
//! assert!( ! set.contains("a") );
//! assert!(   set.contains("b") );
//! ```

pub mod traits;
pub mod weak_key_hash_map;
pub mod ptr_weak_key_hash_map;
pub mod weak_value_hash_map;
pub mod weak_hash_set;
pub mod ptr_weak_hash_set;

mod util;

pub use weak_key_hash_map::WeakKeyHashMap;
pub use ptr_weak_key_hash_map::PtrWeakKeyHashMap;
pub use weak_value_hash_map::WeakValueHashMap;
pub use weak_hash_set::WeakHashSet;
pub use ptr_weak_hash_set::PtrWeakHashSet;
