//! Top-level module for larger tests that don't fit in a particular location.
//!
//! We don't put these in a /tests directory in order to save on compilation time,
//! and in order to help them share code.

#![allow(missing_docs)]
#![allow(clippy::missing_docs_in_private_items)]
#![allow(clippy::print_stderr)]
#![allow(unreachable_pub)]
#![allow(clippy::enum_variant_names)]

mod proptest;
mod symbols;
