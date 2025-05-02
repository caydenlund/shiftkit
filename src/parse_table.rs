//! # Parse Table Module
//!
//! This module provides data structures for representing parse tables used in
//! LR-family parsers (LR(0), LR(1), SLR, and LALR(1)).

use crate::grammar::{Grammar, Symbol, SymbolId};
use std::collections::{HashMap, HashSet};

/// Unique identifier for a parser state
pub type StateId = usize;

/// Unique identifier for a grammar rule
pub type RuleId = (SymbolId, usize); // (non-terminal ID, rule index)

/// Possible actions for an LR parser
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Action {
    /// Shift and transition to the specified state
    Shift(StateId),

    /// Reduce using the specified rule
    Reduce(RuleId),

    /// Accept the input
    Accept,

    /// Error condition
    Error,
}

/// A parse table for LR-family parsers
///
/// # Example
/// ```
/// # use shiftkit::grammar::{Grammar, Symbol};
/// # use shiftkit::parse_table::{ParseTable, Action};
/// # #[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// # enum Terminal {
/// #     Plus,
/// #     Number,
/// # }
/// # impl Symbol for Terminal {}
/// # #[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// # enum NonTerminal {
/// #     Expr,
/// # }
/// # impl Symbol for NonTerminal {}
/// let mut grammar = Grammar::new();
/// let t_eof = 0; // special end-of-file symbol
/// let n_expr = grammar.add_non_terminal(NonTerminal::Expr);
/// let t_plus = grammar.add_terminal(Terminal::Plus);
/// let t_num = grammar.add_terminal(Terminal::Number);
/// grammar.add_rule(n_expr, &[n_expr, t_plus, n_expr]);
/// grammar.add_rule(n_expr, &[t_num]);
/// let mut table = ParseTable::new(grammar);
/// table.add_action(0, t_num, Action::Shift(1));
/// table.set_goto(0, n_expr, 2);
///
/// table.add_action(1, t_plus, Action::Shift(3));
/// table.add_action(1, t_eof, Action::Accept);
///
/// table.add_action(2, t_plus, Action::Reduce((n_expr, 1)));
/// table.add_action(2, t_eof, Action::Reduce((n_expr, 1)));
///
/// table.add_action(3, t_num, Action::Shift(2));
/// table.set_goto(3, n_expr, 4);
///
/// table.add_action(4, t_plus, Action::Reduce((n_expr, 0)));
/// table.add_action(4, t_eof, Action::Reduce((n_expr, 0)));
/// ```
#[derive(Debug, Clone)]
pub struct ParseTable<T: Symbol, N: Symbol> {
    /// The grammar this parse table is built from
    pub grammar: Grammar<T, N>,

    /// Action table: maps (state, terminal) pairs to parser actions
    ///
    /// Multiple actions may be stored for a single pair to detect conflicts.
    action_table: HashMap<(StateId, SymbolId), HashSet<Action>>,

    /// Goto table: maps (state, non-terminal) pairs to new states
    goto_table: HashMap<(StateId, SymbolId), StateId>,

    /// The next state ID to use
    ///
    /// Equal to the total number of states in the parse table.
    next_state: usize,
}

impl<T: Symbol, N: Symbol> ParseTable<T, N> {
    /// Constructs a new parse table for the given grammar
    ///
    /// # Parameters
    /// - `grammar`: The grammar that the parse table will use
    ///
    /// # Returns
    /// A new `ParseTable` for the given grammar
    #[must_use]
    #[inline]
    pub fn new(grammar: Grammar<T, N>) -> Self {
        Self {
            grammar,
            action_table: HashMap::new(),
            goto_table: HashMap::new(),
            next_state: 0,
        }
    }

    /// Adds an action to the action table
    ///
    /// # Parameters
    /// - `state`: The state ID
    /// - `symbol`: The terminal symbol ID
    /// - `action`: The action to take
    pub fn add_action(&mut self, state: StateId, symbol: SymbolId, action: Action) {
        if state >= self.next_state {
            self.next_state = state + 1;
        }

        if let Action::Shift(target_state) = action {
            if target_state >= self.next_state {
                self.next_state = target_state + 1;
            }
        }

        self.action_table
            .entry((state, symbol))
            .or_default()
            .insert(action);
    }

    /// Adds a transition to the goto table
    ///
    /// # Parameters
    /// - `state`: The "from" state ID
    /// - `symbol`: The non-terminal symbol ID
    /// - `target_state`: The target state ID
    pub fn set_goto(&mut self, state: StateId, symbol: SymbolId, target_state: StateId) {
        self.goto_table.insert((state, symbol), target_state);
        // Update state count if necessary
        if state >= self.next_state {
            self.next_state = state + 1;
        }
        if target_state >= self.next_state {
            self.next_state = target_state + 1;
        }
    }

    /// Gets all possible actions for a given state and terminal symbol
    ///
    /// # Parameters
    /// - `state`: The state ID
    /// - `symbol`: The terminal symbol ID
    ///
    /// # Returns
    /// A set of all possible actions for the given state and symbol
    #[must_use]
    #[inline]
    pub fn get_actions(&self, state: StateId, symbol: SymbolId) -> Option<&HashSet<Action>> {
        self.action_table.get(&(state, symbol))
    }

    /// Gets the "goto" destination state for a given state and non-terminal symbol
    ///
    /// # Parameters
    /// - `state`: The state ID
    /// - `symbol`: The non-terminal symbol ID
    ///
    /// # Returns
    /// The target state, or `None` if no goto is defined
    #[must_use]
    #[inline]
    pub fn get_goto(&self, state: StateId, symbol: SymbolId) -> Option<StateId> {
        self.goto_table.get(&(state, symbol)).copied()
    }

    /// Returns the number of states in the parse table
    ///
    /// # Returns
    /// The number of states in the parse table
    #[must_use]
    #[inline]
    pub const fn len(&self) -> usize {
        self.next_state
    }

    /// Reports whether this parse table has no states
    ///
    /// # Returns
    /// True if this parse table has no states
    #[must_use]
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::{Grammar, Symbol};

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum Terminal {
        X,
        Y,
        Z,
    }
    impl Symbol for Terminal {}

    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    enum NonTerminal {
        S,
        A,
    }
    impl Symbol for NonTerminal {}

    // Helper function to create a simple grammar for testing
    fn create_test_grammar() -> Grammar<Terminal, NonTerminal> {
        let mut grammar = Grammar::new();
        let n_s = grammar.add_non_terminal(NonTerminal::S);
        let n_a = grammar.add_non_terminal(NonTerminal::A);
        let t_x = grammar.add_terminal(Terminal::X);
        let t_y = grammar.add_terminal(Terminal::Y);
        let t_z = grammar.add_terminal(Terminal::Z);

        grammar.add_rule(n_s, &[n_a]); // S => A
        grammar.add_rule(n_a, &[t_x, n_a, t_y]); // A => x A y
        grammar.add_rule(n_a, &[t_z]); // A => z

        grammar
    }

    #[test]
    fn test_new_parse_table() {
        let grammar = create_test_grammar();
        let table = ParseTable::new(grammar);

        assert!(table.is_empty());
        assert_eq!(table.len(), 0);
        assert!(table.action_table.is_empty());
        assert!(table.goto_table.is_empty());
    }

    #[test]
    fn test_add_action() {
        let grammar = create_test_grammar();
        let mut table = ParseTable::new(grammar);

        // Test adding a single action
        table.add_action(0, 0, Action::Shift(1));
        assert_eq!(table.len(), 2); // States 0 and 1 exist now
        assert_eq!(table.get_actions(0, 0).unwrap().len(), 1);
        assert!(table.get_actions(0, 0).unwrap().contains(&Action::Shift(1)));

        // Test adding multiple actions to same state/symbol (conflict)
        table.add_action(0, 0, Action::Reduce((0, 0)));
        assert_eq!(table.get_actions(0, 0).unwrap().len(), 2);
        assert!(table.get_actions(0, 0).unwrap().contains(&Action::Shift(1)));
        assert!(table
            .get_actions(0, 0)
            .unwrap()
            .contains(&Action::Reduce((0, 0))));

        // Test adding action that increases state count
        table.add_action(5, 0, Action::Shift(6));
        assert_eq!(table.len(), 7); // Now up to state 6
    }

    #[test]
    fn test_set_goto() {
        let grammar = create_test_grammar();
        let mut table = ParseTable::new(grammar);

        // Test basic goto setting
        table.set_goto(0, 0, 1);
        assert_eq!(table.get_goto(0, 0), Some(1));
        assert_eq!(table.len(), 2);

        // Test overwriting existing goto
        table.set_goto(0, 0, 2);
        assert_eq!(table.get_goto(0, 0), Some(2));
        assert_eq!(table.len(), 3);

        // Test goto with higher state numbers
        table.set_goto(10, 1, 20);
        assert_eq!(table.get_goto(10, 1), Some(20));
        assert_eq!(table.len(), 21);
    }

    #[test]
    fn test_get_actions() {
        let grammar = create_test_grammar();
        let mut table = ParseTable::new(grammar);

        // Test getting non-existent actions
        assert!(table.get_actions(0, 0).is_none());

        // Test getting existing actions
        table.add_action(0, 0, Action::Shift(1));
        assert_eq!(table.get_actions(0, 0).unwrap().len(), 1);

        // Test getting actions for non-existent state
        assert!(table.get_actions(1, 0).is_none());
    }

    #[test]
    fn test_get_goto() {
        let grammar = create_test_grammar();
        let mut table = ParseTable::new(grammar);

        // Test getting non-existent goto
        assert!(table.get_goto(0, 0).is_none());

        // Test getting existing goto
        table.set_goto(0, 0, 1);
        assert_eq!(table.get_goto(0, 0), Some(1));

        // Test getting goto for non-existent state
        assert!(table.get_goto(1, 0).is_none());
    }

    #[test]
    fn test_len_and_is_empty() {
        let grammar = create_test_grammar();
        let mut table = ParseTable::new(grammar);

        assert!(table.is_empty());
        assert_eq!(table.len(), 0);

        // Adding actions should increase state count
        table.add_action(0, 0, Action::Shift(1));
        assert!(!table.is_empty());
        assert_eq!(table.len(), 2);

        // Adding higher state numbers should increase count
        table.add_action(5, 0, Action::Shift(6));
        assert_eq!(table.len(), 7);

        // Goto operations should also affect state count
        table.set_goto(10, 0, 20);
        assert_eq!(table.len(), 21);
    }

    #[test]
    fn test_action_enum() {
        // Test Action enum variants and equality
        let shift1 = Action::Shift(1);
        let shift2 = Action::Shift(2);
        let reduce1 = Action::Reduce((0, 0));
        let reduce2 = Action::Reduce((0, 1));
        let accept = Action::Accept;
        let error = Action::Error;

        assert_eq!(shift1, Action::Shift(1));
        assert_ne!(shift1, shift2);
        assert_eq!(reduce1, Action::Reduce((0, 0)));
        assert_ne!(reduce1, reduce2);
        assert_eq!(accept, Action::Accept);
        assert_eq!(error, Action::Error);
        assert_ne!(shift1, reduce1);
    }

    #[test]
    fn test_conflict_detection() {
        let grammar = create_test_grammar();
        let mut table = ParseTable::new(grammar);

        // Add conflicting actions
        table.add_action(0, 0, Action::Shift(1));
        table.add_action(0, 0, Action::Reduce((0, 0)));

        let actions = table.get_actions(0, 0).unwrap();
        assert_eq!(actions.len(), 2);
        assert!(actions.contains(&Action::Shift(1)));
        assert!(actions.contains(&Action::Reduce((0, 0))));

        // Add another conflict (shift-shift)
        table.add_action(0, 0, Action::Shift(2));
        let actions = table.get_actions(0, 0).unwrap();
        assert_eq!(actions.len(), 3);
    }

    #[test]
    fn test_accept_and_error_actions() {
        let grammar = create_test_grammar();
        let mut table = ParseTable::new(grammar);

        table.add_action(0, 0, Action::Accept);
        table.add_action(1, 1, Action::Error);

        let accept_actions = table.get_actions(0, 0).unwrap();
        assert_eq!(accept_actions.len(), 1);
        assert!(accept_actions.contains(&Action::Accept));

        let error_actions = table.get_actions(1, 1).unwrap();
        assert_eq!(error_actions.len(), 1);
        assert!(error_actions.contains(&Action::Error));
    }

    #[test]
    fn test_rule_id_handling() {
        let grammar = create_test_grammar();
        let mut table = ParseTable::new(grammar);

        // Test reduce actions with different rule IDs
        table.add_action(0, 0, Action::Reduce((0, 0)));
        table.add_action(0, 0, Action::Reduce((0, 1)));
        table.add_action(0, 0, Action::Reduce((1, 0)));

        let actions = table.get_actions(0, 0).unwrap();
        assert_eq!(actions.len(), 3);
        assert!(actions.contains(&Action::Reduce((0, 0))));
        assert!(actions.contains(&Action::Reduce((0, 1))));
        assert!(actions.contains(&Action::Reduce((1, 0))));
    }
}
