# `shiftkit`

**`shiftkit`** is a Rust library for generating efficient **LR**, **SLR**, and **LALR** parsers from grammar definitions.

It aims to provide a clean, modular, and modern API for parser generation, with a focus on flexibility, diagnostics, and performance---all written idiomatically in Rust.

---

## Planned Features

- Define grammars using Rust data structures (not DSLs or macros — unless you want to!)
- Generate parse tables for **LR(0)**, **LR(1)**, **SLR(1)**, and **LALR(1)** parsers
- Generate parse tables at compile-time, statically embedded in the binary
- Resolve and report conflicts (shift/reduce, reduce/reduce) with detailed diagnostics
- Backed by formal parsing theory, powered by efficient data structures
- Tools to inspect states, lookaheads, and parser behavior

---

## Goals

- Be **approachable** to compiler beginners and usable by experts
- Stay **modular**---you can swap out pieces (e.g., custom lexers or grammar builders)
- Offer great **error messages** for grammar issues
- Include **powerful tooling**, like command-line generation or visualization

---

## Status

`shiftkit` is in early development and APIs are still being designed.

If you’re interested in contributing or testing early features, feel free to reach out or open an issue!

---

## License

Dual-licensed under **MIT** or **Apache-2.0**---choose whichever you prefer.

---

## Contributions Welcome

Want to help design the API, test parsing edge cases, or implement LALR(1) lookahead logic? Open an issue---let's build this together.
