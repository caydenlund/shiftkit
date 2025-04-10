//! shiftkit - A Rust library for generating LR and LALR parsers
//!
//! This crate provides data structures and algorithms to generate bottom-up
//! parsers from grammar definitions, with support for LR(0), LR(1), SLR(1),
//! and LALR(1) parsers.

#![warn(
    clippy::all,
    clippy::cargo,
    clippy::missing_docs_in_private_items,
    clippy::nursery,
    clippy::pedantic,
    missing_docs,
    rustdoc::all
)]

pub mod grammar;
pub mod parse_table;
