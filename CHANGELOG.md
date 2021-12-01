# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog] and this project adheres to
[Semantic Versioning].

[Keep a Changelog]: http://keepachangelog.com/en/1.0.0/
[Semantic Versioning]: http://semver.org/spec/v2.0.0.html

## [Next Release]

## [0.3.2] - 2021-12-01

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
- documentation
- a test that was breaking on an older `rustc`

## [0.2.0] - 2018-05-22

### Renamed
- from `WeakElement::expired` to `WeakElement::is_expired`

### Improved
- documentation

## [0.1.3] - 2018-05-22

### Added
- documentation of minimum supported `rustc`
- a test

## [0.1.2] - 2018-05-21

### Added
- `WeakKeyHashMap::{get_key, get_both, get_both_mut}` methods
- `WeakWeakHashMap::{get_key, get_both}` methods
- `WeakHashSet::get` method

### Changed
- Values stored behind `Rc`s can now be `?Sized`.

### Removed
- `struct RcKey<K>`

### Improved
- documentation

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
