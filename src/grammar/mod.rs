//! # Grammar Module
//!
//! This module provides core data structures for representing a context-free grammar,
//! suitable for use in parser generators (e.g., LR, SLR, or LALR parsers).
//!
//! Each symbol (terminal or non-terminal) is assigned a unique ID (`SymbolId`) and stored
//! with metadata like name and kind. Rules are associated with non-terminals and consist
//! of sequences of symbol IDs representing grammar productions.

use std::collections::HashMap;
use std::hash::Hash;

/// Describes a datatype that can be used as a grammar symbol
pub trait Symbol: Clone + Eq + PartialEq + Hash {}

/// A grammar symbol: either a terminal (token) or non-terminal (grammar production)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum GrammarSymbol<T: Symbol, N: Symbol> {
    /// A token or literal input symbol (e.g., "+", "num")
    Terminal(T),

    /// A grammar rule (e.g., Expr, Term)
    NonTerminal(N),

    /// A special end-of-file token
    EndOfFile,
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
/// # use shiftkit::grammar::{Grammar, Symbol};
/// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// enum Terminal {
///     Plus,
///     Number,
/// }
/// impl Symbol for Terminal {}
/// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// enum NonTerminal {
///     Expr,
/// }
/// impl Symbol for NonTerminal {}
/// let mut grammar = Grammar::new();
/// let n_expr_id = grammar.add_non_terminal(NonTerminal::Expr);
/// let t_plus_id = grammar.add_terminal(Terminal::Plus);
/// let t_num_id = grammar.add_terminal(Terminal::Number);
/// grammar.add_rule(n_expr_id, &[n_expr_id, t_plus_id, n_expr_id]);
/// grammar.add_rule(n_expr_id, &[t_num_id]);
/// ```
#[derive(Debug, Clone)]
pub struct Grammar<T: Symbol, N: Symbol> {
    /// All symbols in the grammar
    ///
    /// The index into this vector is the `SymbolId`.
    pub symbols: Vec<GrammarSymbol<T, N>>,

    /// For each non-terminal (by `SymbolId`), a list of production rules
    ///
    /// Each rule is a vector of symbol IDs.
    pub rules: Vec<Vec<Vec<SymbolId>>>,

    /// The optional start symbol for the grammar
    pub start: Option<SymbolId>,

    /// Internal map for deduplicating symbol entries
    symbol_map: HashMap<GrammarSymbol<T, N>, SymbolId>,
}

impl<T: Symbol, N: Symbol> Grammar<T, N> {
    /// Creates a new, empty grammar
    ///
    /// # Returns
    /// A fresh `Grammar` instance with no symbols or rules
    #[must_use]
    pub fn new() -> Self {
        let mut g = Self {
            symbols: Vec::new(),
            rules: Vec::new(),
            start: None,
            symbol_map: HashMap::new(),
        };
        // Add the end-of-file symbol with ID 0
        g.add_symbol(GrammarSymbol::EndOfFile);
        g
    }

    /// Adds a new symbol to the grammar
    ///
    /// If the symbol already exists, its existing `SymbolId` is returned.
    /// Otherwise, it is inserted and assigned a new ID.
    ///
    /// # Parameters
    /// - `sym`: The symbol to add to the grammar
    ///
    /// # Returns
    /// A `SymbolId` for the added or existing symbol
    pub fn add_symbol(&mut self, sym: GrammarSymbol<T, N>) -> SymbolId {
        if let Some(&id) = self.symbol_map.get(&sym) {
            return id;
        }

        let id = self.symbols.len();
        self.symbols.push(sym.clone());

        // Always push an empty rule list, even for terminals
        self.rules.push(Vec::new());

        self.symbol_map.insert(sym, id);
        id
    }

    /// Adds a new terminal symbol to the grammar
    ///
    /// If the symbol already exists in the grammar, its existing `SymbolId` is returned.
    /// Otherwise, it is inserted and assigned a new ID.
    ///
    /// # Parameters
    /// - `term`: The terminal symbol to add to the grammar
    ///
    /// # Returns
    /// A `SymbolId` for the added or existing terminal symbol
    pub fn add_terminal(&mut self, term: T) -> SymbolId {
        self.add_symbol(GrammarSymbol::Terminal(term))
    }

    /// Adds a new non-terminal symbol to the grammar
    ///
    /// If the symbol already exists, its existing `SymbolId` is returned.
    /// Otherwise, it is inserted and assigned a new ID.
    ///
    /// # Parameters
    /// - `non_term`: The non-terminal symbol to add to the grammar
    ///
    /// # Returns
    /// A `SymbolId` for the added or existing symbol
    pub fn add_non_terminal(&mut self, non_term: N) -> SymbolId {
        self.add_symbol(GrammarSymbol::NonTerminal(non_term))
    }

    /// Adds a production rule to a non-terminal symbol
    ///
    /// # Parameters
    /// - `non_terminal`: The `SymbolId` of a non-terminal symbol
    /// - `production`: A slice of `SymbolId`s representing the right-hand side of the rule
    ///
    /// # Panics
    /// If the given `non_terminal` ID does not refer to a non-terminal symbol
    pub fn add_rule(&mut self, non_terminal: SymbolId, production: &[SymbolId]) {
        assert!(
            matches!(
                self.get_symbol(non_terminal),
                Some(GrammarSymbol::NonTerminal(_))
            ),
            "Symbol ID {non_terminal} is not a non-terminal"
        );
        self.rules[non_terminal].push(production.to_vec());
    }

    /// Retrieves a symbol by its ID
    ///
    /// # Parameters
    /// - `id`: The symbol's unique ID (`SymbolId`)
    ///
    /// # Returns
    /// The symbol with the given `SymbolId`
    #[must_use]
    pub fn get_symbol(&self, id: SymbolId) -> Option<&GrammarSymbol<T, N>> {
        self.symbols.get(id)
    }

    /// Sets the given symbol as the "start" symbol
    ///
    /// # Parameters
    /// - `non_terminal`: The `SymbolId` of a non-terminal symbol
    ///
    /// # Panics
    /// If the given `non_terminal` ID does not refer to a non-terminal symbol
    pub fn set_start(&mut self, non_terminal: SymbolId) {
        self.start = Some(non_terminal);
    }
}

impl<T: Symbol, N: Symbol> Default for Grammar<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::{Grammar, GrammarSymbol, Symbol};

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum NonTerminal {
        Expr,
        Term,
    }
    impl Symbol for Terminal {}

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum Terminal {
        Plus,
        Number,
    }
    impl Symbol for NonTerminal {}

    #[test]
    fn test_add_symbol() {
        let mut grammar = Grammar::new();

        // Add some symbols and assert that the correct SymbolId is returned
        let expr_id = grammar.add_non_terminal(NonTerminal::Expr);
        let term_id = grammar.add_non_terminal(NonTerminal::Term);
        let plus_id = grammar.add_terminal(Terminal::Plus);

        // Verify the symbol ids are as expected (increasing order starting from 1)
        assert_eq!(expr_id, 1);
        assert_eq!(term_id, 2);
        assert_eq!(plus_id, 3);

        // Verify the correct symbols are stored
        assert_eq!(
            grammar.get_symbol(expr_id),
            Some(&GrammarSymbol::NonTerminal(NonTerminal::Expr))
        );
        assert_eq!(
            grammar.get_symbol(term_id),
            Some(&GrammarSymbol::NonTerminal(NonTerminal::Term))
        );
        assert_eq!(
            grammar.get_symbol(plus_id),
            Some(&GrammarSymbol::Terminal(Terminal::Plus))
        );
    }

    #[test]
    fn test_add_existing_symbol() {
        let mut grammar = Grammar::<Terminal, NonTerminal>::new();

        // Add symbol once
        let expr_id1 = grammar.add_non_terminal(NonTerminal::Expr);

        // Add the same symbol again and assert we get the same ID
        let expr_id2 = grammar.add_non_terminal(NonTerminal::Expr);

        // The ID should be the same
        assert_eq!(expr_id1, expr_id2);
    }

    #[test]
    fn test_add_rule() {
        let mut grammar = Grammar::new();

        let expr_id = grammar.add_non_terminal(NonTerminal::Expr);
        let term_id = grammar.add_non_terminal(NonTerminal::Term);
        let plus_id = grammar.add_terminal(Terminal::Plus);

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

        let expr_id = grammar.add_non_terminal(NonTerminal::Expr);
        let term_id = grammar.add_non_terminal(NonTerminal::Term);
        let plus_id = grammar.add_terminal(Terminal::Plus);

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

            let expr_id = grammar.add_non_terminal(NonTerminal::Expr);
            let num_id = grammar.add_terminal(Terminal::Number);

            grammar.add_rule(num_id, &[expr_id]);
        });

        assert!(result.is_err());
    }

    #[test]
    fn test_symbol_lookup() {
        let mut grammar = Grammar::new();

        let expr_id = grammar.add_non_terminal(NonTerminal::Expr);
        let num_id = grammar.add_terminal(Terminal::Number);

        // Check that the symbol kinds are correctly looked up
        assert_eq!(
            grammar.get_symbol(expr_id),
            Some(&GrammarSymbol::NonTerminal(NonTerminal::Expr))
        );
        assert_eq!(
            grammar.get_symbol(num_id),
            Some(&GrammarSymbol::Terminal(Terminal::Number))
        );
        assert_eq!(grammar.get_symbol(999), None); // Non-existent symbol ID
    }

    #[test]
    fn test_start_symbol() {
        let mut grammar = Grammar::<Terminal, NonTerminal>::new();

        let expr_id = grammar.add_non_terminal(NonTerminal::Expr);

        // Set the start symbol
        grammar.set_start(expr_id);

        // Check that the start symbol is correctly set
        assert_eq!(grammar.start, Some(expr_id));
    }

    #[test]
    fn test_empty_grammar() {
        let grammar = Grammar::<Terminal, NonTerminal>::new();

        // An empty grammar should have 1 symbol (end of file), no rules,
        // and no start symbol
        assert_eq!(grammar.symbols.len(), 1);
        assert_eq!(grammar.rules.len(), 1);
        assert_eq!(grammar.start, None);
    }

    #[test]
    fn test_combined_usage() {
        let mut grammar = Grammar::new();

        let expr_id = grammar.add_non_terminal(NonTerminal::Expr);
        let term_id = grammar.add_non_terminal(NonTerminal::Term);
        let plus_id = grammar.add_terminal(Terminal::Plus);
        let num_id = grammar.add_terminal(Terminal::Number);

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
