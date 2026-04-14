# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog] and this project adheres to
[Semantic Versioning].

[Keep a Changelog]: http://keepachangelog.com/en/1.0.0/
[Semantic Versioning]: http://semver.org/spec/v2.0.0.html

## [Next Release]

### Added

- High-coverage unit tests for the hash table backend.
- Property tests for all of the exposed map and set types.
- Benchmarks based on `criterion`.

- Added APIs to map types to match with stdlib `HashMap`:
  - `extract_if`
  - `get_disjoint_mut`, `get_both_disjoint_mut`
  - `into_keys`
  - `into_values`
  - `remove_entry`
  - `shrink_to`
  - `try_reserve`
  - `From<[(K, V); N]>`
  - `Entry::and_modify`
  - `Entry::insert_entry`
  - `Entry::or_insert_with_key`
  - `VacantEntry::insert_entry`.

- Added APIs to set types to match with stdlib `HashSet`:
  - `difference`
  - `extract_if`
  - `intersection`
  - `is_disjoint`
  - `is_superset`
  - `shrink_to`
  - `symmetric_difference`
  - `take`
  - `try_reserve`
  - `union`
  - `BitAnd`
  - `BitOr`
  - `BitXor`
  - `From<[T;N]>`
  - `Sub`

### Fixed

### Changed (visible)

- All hash-tables now use a new backend based on [`hashbrown`]
  for improved speed and correctness.
  (Benchmarks report a speedup around 30-50%.)
- The Minimum Supported Rust Version is now 1.65.
  (This is necessary to use `hashbrown`.)
- The default capacity for new tables is now zero.
- Changed `load_factor()` to return a value closer to the table's
  actual load factor.

### Changed (internal)

- Numerous Clippy warnings are now enabled.
- The Rust Edition is now 2021.
- We no longer rely on floating-point except in methods that return a
  floating-point result.
- The `Debug` output is slightly different.
- The source is now formatted according to the Rust style guide,
  using `cargo fmt`.
- Allocation sizes are now slightly different.
- The output of `Debug` is now slightly different.
- Because of `hashbrown` internals, capacity calculations can behave
  differently.
- Tests have been moved to a `tests` submodule, so that they can
  share code.

### Fixed

- The `retain()` and `remove_expired()` methods no longer
  skip elements that changed position due to other elements having been
  removed. ([github#22])
- Fix a bug in `load_factor()` calculation where it would return
  `inf` for a zero-capacity table.

### Documentation
  - Cleaned up documentation that referred to sets as maps,
    or claimed that they had separate keys and values.

## [0.3.2] - 2021-12-01

### Documentation
- listed asymptotic time complexities for each operation

## [0.3.1] - 2021-11-30

### Added
- `no_std` compatibility (h/t @tsao-chi)

## [0.2.4] - 2020-06-27

### Fixed
- Bad bucket selection on collision (h/t Andrew Browne
  `<dersaidin@dersaidin.net>`).

## [0.2.3] - 2018-05-30

### Fixed
- Use `Rc::ptr_eq` to compare `Rc`s by address.

## [0.2.2] - 2018-05-22

### Fixed
- Weak–weak submap operations were missing a line of code.

### Added
- `{PtrWeakHashSet,PtrWeakKeyHashMap}::is_empty()` methods.

## [0.2.1] - 2018-05-22

### Fixed
- a test that was breaking on an older `rustc`

### Documention
- improved

## [0.2.0] - 2018-05-22

### Renamed
- from `WeakElement::expired` to `WeakElement::is_expired`

### Documention
- improved

## [0.1.3] - 2018-05-22

### Testing
- added a test

### Documention
- minimum supported `rustc`

## [0.1.2] - 2018-05-21

### Added
- `WeakKeyHashMap::{get_key, get_both, get_both_mut}` methods
- `WeakWeakHashMap::{get_key, get_both}` methods
- `WeakHashSet::get` method

### Changed
- Values stored behind `Rc`s can now be `?Sized`.

### Removed
- `struct RcKey<K>`

### Documentation
- improved

## [0.1.1] - 2018-03-05

Initial release.

[Next Release]: <https://github.com/tov/weak-table-rs/compare/v0.3.2...HEAD>
[0.3.2]: <https://github.com/tov/weak-table-rs/compare/v0.3.1...v0.3.2>
[0.3.1]: <https://github.com/tov/weak-table-rs/compare/v0.3.1-alpha.0...v0.3.1>
[0.2.4]: <https://github.com/tov/weak-table-rs/compare/0.2.3...0.2.4>
[0.2.3]: <https://github.com/tov/weak-table-rs/compare/0.2.2...0.2.3>
[0.2.2]: <https://github.com/tov/weak-table-rs/compare/0.2.1...0.2.2>
[0.2.1]: <https://github.com/tov/weak-table-rs/compare/0.2.0...0.2.1>
[0.2.0]: <https://github.com/tov/weak-table-rs/compare/0.1.3...0.2.0>
[0.1.3]: <https://github.com/tov/weak-table-rs/compare/0.1.2...0.1.3>
[0.1.2]: <https://github.com/tov/weak-table-rs/compare/0.1.1...0.1.2>
[0.1.1]: <https://github.com/tov/weak-table-rs/tree/0.1.1>
[`weak-table`]: <https://crates.io/crates/weak-table>
[`hashbrown`]: <https://docs.rs/hashbrown/latest/hashbrown/struct.HashTable.html>
[github#22]: <https://github.com/tov/weak-table-rs/issues/22>
