//! # Grammar Module
//!
//! This module provides core data structures for representing a context-free grammar,
//! suitable for use in parser generators (e.g., LR, SLR, or LALR parsers).
//!
//! Each symbol (terminal or non-terminal) is assigned a unique ID (`SymbolId`) and stored
//! with metadata like name and kind. Rules are associated with non-terminals and consist
//! of sequences of symbol IDs representing grammar productions.

use std::collections::HashMap;

/// The kind of a grammar symbol---either a terminal (token) or non-terminal (grammar rule)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymbolKind {
    /// A token or literal input symbol (e.g., "+", "num")
    Terminal,

    /// A grammar rule (e.g., Expr, Term)
    NonTerminal,
}

/// A unique identifier for a symbol (either terminal or non-terminal)
///
/// These IDs index into the `Grammar::symbols` vector.
pub type SymbolId = usize;

/// Represents a context-free grammar using symbol IDs and production rules
///
/// Terminals and non-terminals are stored in a shared `symbols` vector.
/// Rules are attached only to non-terminal symbols.
///
/// # Example
/// ```
/// # use shiftkit::grammar::{Grammar, SymbolKind};
/// let mut grammar = Grammar::new();
/// let n_expr = grammar.add_symbol(SymbolKind::NonTerminal, "Expr");
/// let t_plus = grammar.add_symbol(SymbolKind::Terminal, "+");
/// let t_num = grammar.add_symbol(SymbolKind::Terminal, "num");
/// grammar.add_rule(n_expr, &[n_expr, t_plus, n_expr]);
/// grammar.add_rule(n_expr, &[t_num]);
/// ```
#[derive(Debug, Clone, Default)]
pub struct Grammar {
    /// All symbols in the grammar: `(kind, name)`
    ///
    /// The index into this vector is the `SymbolId`.
    pub symbols: Vec<(SymbolKind, String)>,

    /// For each non-terminal (by `SymbolId`), a list of production rules
    ///
    /// Each rule is a vector of symbol IDs.
    pub rules: Vec<Vec<Vec<SymbolId>>>,

    /// The optional start symbol for the grammar
    pub start: Option<SymbolId>,

    /// Internal map for deduplicating symbol entries
    symbol_map: HashMap<(SymbolKind, String), SymbolId>,
}

impl Grammar {
    /// Creates a new, empty grammar
    ///
    /// # Returns
    /// A fresh `Grammar` instance with no symbols or rules.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds a new symbol to the grammar
    ///
    /// If the symbol already exists (same name and kind), its existing `SymbolId` is returned.
    /// Otherwise, it is inserted and assigned a new ID.
    ///
    /// # Parameters
    /// - `kind`: The kind of symbol (`Terminal` or `NonTerminal`)
    /// - `name`: The name of the symbol (used for display, debugging, and lookup)
    ///
    /// # Returns
    /// A `SymbolId` for the added or existing symbol.
    pub fn add_symbol<S: Into<String>>(&mut self, kind: SymbolKind, name: S) -> SymbolId {
        let name = name.into();
        let key = (kind, name);

        if let Some(&id) = self.symbol_map.get(&key) {
            return id;
        }

        let id = self.symbols.len();
        self.symbols.push(key.clone());

        // Always push an empty rule list, even for terminals
        self.rules.push(Vec::new());

        self.symbol_map.insert(key, id);
        id
    }

    /// Adds a production rule to a non-terminal symbol
    ///
    /// # Parameters
    /// - `non_terminal`: The `SymbolId` of a non-terminal symbol.
    /// - `production`: A slice of `SymbolId`s representing the right-hand side of the rule.
    ///
    /// # Panics
    /// If the given `non_terminal` ID does not refer to a non-terminal symbol.
    pub fn add_rule(&mut self, non_terminal: SymbolId, production: &[SymbolId]) {
        if !matches!(
            self.symbol_kind(non_terminal),
            Some(SymbolKind::NonTerminal)
        ) {
            panic!("Symbol ID {non_terminal} is not a non-terminal");
        }
        self.rules[non_terminal].push(production.to_vec());
    }

    /// Retrieves the name of a symbol by its ID
    ///
    /// # Parameters
    /// - `id`: The symbol's unique ID (`SymbolId`)
    ///
    /// # Returns
    /// An optional string slice of the symbol's name.
    #[must_use]
    pub fn symbol_name(&self, id: SymbolId) -> Option<&str> {
        self.symbols.get(id).map(|(_, name)| name.as_str())
    }

    /// Retrieves the kind of a symbol by its ID
    ///
    /// # Parameters
    /// - `id`: The symbol's unique ID (`SymbolId`)
    ///
    /// # Returns
    /// An optional `SymbolKind` if the ID exists.
    #[must_use]
    pub fn symbol_kind(&self, id: SymbolId) -> Option<SymbolKind> {
        self.symbols.get(id).map(|(kind, _)| *kind)
    }

    /// Sets the given symbol as the "start" symbol
    ///
    /// # Parameters
    /// - `non_terminal`: The `SymbolId` of a non-terminal symbol.
    ///
    /// # Panics
    /// If the given `non_terminal` ID does not refer to a non-terminal symbol.
    pub fn set_start(&mut self, non_terminal: SymbolId) {
        self.start = Some(non_terminal);
    }
}

#[cfg(test)]
mod tests {
    use super::{Grammar, SymbolKind};

    #[test]
    fn test_add_symbol() {
        let mut grammar = Grammar::new();

        // Add some symbols and assert that the correct SymbolId is returned
        let expr_id = grammar.add_symbol(SymbolKind::NonTerminal, "Expr");
        let term_id = grammar.add_symbol(SymbolKind::NonTerminal, "Term");
        let plus_id = grammar.add_symbol(SymbolKind::Terminal, "+");

        // Verify the symbol ids are as expected (increasing order starting from 0)
        assert_eq!(expr_id, 0);
        assert_eq!(term_id, 1);
        assert_eq!(plus_id, 2);

        // Verify the correct symbols are stored
        assert_eq!(grammar.symbol_name(expr_id), Some("Expr"));
        assert_eq!(grammar.symbol_name(term_id), Some("Term"));
        assert_eq!(grammar.symbol_name(plus_id), Some("+"));

        // Verify the kind of symbols
        assert_eq!(grammar.symbol_kind(expr_id), Some(SymbolKind::NonTerminal));
        assert_eq!(grammar.symbol_kind(term_id), Some(SymbolKind::NonTerminal));
        assert_eq!(grammar.symbol_kind(plus_id), Some(SymbolKind::Terminal));
    }

    #[test]
    fn test_add_existing_symbol() {
        let mut grammar = Grammar::new();

        // Add symbol once
        let expr_id1 = grammar.add_symbol(SymbolKind::NonTerminal, "Expr");

        // Add the same symbol again and assert we get the same ID
        let expr_id2 = grammar.add_symbol(SymbolKind::NonTerminal, "Expr");

        // The ID should be the same
        assert_eq!(expr_id1, expr_id2);
    }

    #[test]
    fn test_add_rule() {
        let mut grammar = Grammar::new();

        let expr_id = grammar.add_symbol(SymbolKind::NonTerminal, "Expr");
        let term_id = grammar.add_symbol(SymbolKind::NonTerminal, "Term");
        let plus_id = grammar.add_symbol(SymbolKind::Terminal, "+");

        // Add a rule for Expr -> Expr + Term
        grammar.add_rule(expr_id, &[expr_id, plus_id, term_id]);

        // Verify that the rule has been added correctly
        let rules = &grammar.rules[expr_id];
        assert_eq!(rules.len(), 1);
        assert_eq!(rules[0], vec![expr_id, plus_id, term_id]);
    }

    #[test]
    fn test_add_multiple_rules() {
        let mut grammar = Grammar::new();

        let expr_id = grammar.add_symbol(SymbolKind::NonTerminal, "Expr");
        let term_id = grammar.add_symbol(SymbolKind::NonTerminal, "Term");
        let plus_id = grammar.add_symbol(SymbolKind::Terminal, "+");

        // Add multiple rules for Expr
        grammar.add_rule(expr_id, &[expr_id, plus_id, term_id]);
        grammar.add_rule(expr_id, &[term_id]);

        // Verify that both rules are added correctly
        let rules = &grammar.rules[expr_id];
        assert_eq!(rules.len(), 2);
        assert_eq!(rules[0], vec![expr_id, plus_id, term_id]);
        assert_eq!(rules[1], vec![term_id]);
    }

    #[test]
    fn test_invalid_add_rule() {
        // Try adding a rule to a terminal symbol, should panic
        let result = std::panic::catch_unwind(|| {
            let mut grammar = Grammar::new();

            let expr_id = grammar.add_symbol(SymbolKind::NonTerminal, "Expr");
            let num_id = grammar.add_symbol(SymbolKind::Terminal, "num");

            grammar.add_rule(num_id, &[expr_id]);
        });

        assert!(result.is_err());
    }

    #[test]
    fn test_symbol_kind_lookup() {
        let mut grammar = Grammar::new();

        let expr_id = grammar.add_symbol(SymbolKind::NonTerminal, "Expr");
        let num_id = grammar.add_symbol(SymbolKind::Terminal, "num");

        // Check that the symbol kinds are correctly looked up
        assert_eq!(grammar.symbol_kind(expr_id), Some(SymbolKind::NonTerminal));
        assert_eq!(grammar.symbol_kind(num_id), Some(SymbolKind::Terminal));
        assert_eq!(grammar.symbol_kind(999), None); // Non-existent symbol ID
    }

    #[test]
    fn test_symbol_name_lookup() {
        let mut grammar = Grammar::new();

        let expr_id = grammar.add_symbol(SymbolKind::NonTerminal, "Expr");
        let num_id = grammar.add_symbol(SymbolKind::Terminal, "num");

        // Check that the symbol names are correctly looked up
        assert_eq!(grammar.symbol_name(expr_id), Some("Expr"));
        assert_eq!(grammar.symbol_name(num_id), Some("num"));
        assert_eq!(grammar.symbol_name(999), None); // Non-existent symbol ID
    }

    #[test]
    fn test_start_symbol() {
        let mut grammar = Grammar::new();

        let expr_id = grammar.add_symbol(SymbolKind::NonTerminal, "Expr");

        // Set the start symbol
        grammar.set_start(expr_id);

        // Check that the start symbol is correctly set
        assert_eq!(grammar.start, Some(expr_id));
    }

    #[test]
    fn test_empty_grammar() {
        let grammar = Grammar::new();

        // An empty grammar should have no symbols, no rules, and no start symbol
        assert_eq!(grammar.symbols.len(), 0);
        assert_eq!(grammar.rules.len(), 0);
        assert_eq!(grammar.start, None);
    }

    #[test]
    fn test_combined_usage() {
        let mut grammar = Grammar::new();

        let expr_id = grammar.add_symbol(SymbolKind::NonTerminal, "Expr");
        let term_id = grammar.add_symbol(SymbolKind::NonTerminal, "Term");
        let plus_id = grammar.add_symbol(SymbolKind::Terminal, "+");
        let num_id = grammar.add_symbol(SymbolKind::Terminal, "num");

        // Define grammar rules
        grammar.add_rule(expr_id, &[expr_id, plus_id, term_id]);
        grammar.add_rule(expr_id, &[term_id]);
        grammar.add_rule(term_id, &[term_id, plus_id, num_id]);
        grammar.add_rule(term_id, &[num_id]);

        // Set start symbol
        grammar.set_start(expr_id);

        // Verify grammar rules for Expr
        let rules = &grammar.rules[expr_id];
        assert_eq!(rules.len(), 2);
        assert_eq!(rules[0], vec![expr_id, plus_id, term_id]);
        assert_eq!(rules[1], vec![term_id]);

        // Verify grammar rules for Term
        let rules = &grammar.rules[term_id];
        assert_eq!(rules.len(), 2);
        assert_eq!(rules[0], vec![term_id, plus_id, num_id]);
        assert_eq!(rules[1], vec![num_id]);

        // Verify start symbol
        assert_eq!(grammar.start, Some(expr_id));
    }
}
