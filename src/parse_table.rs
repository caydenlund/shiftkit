//! # Parse Table Module
//!
//! This module provides data structures for representing parse tables used in
//! LR-family parsers (LR(0), LR(1), SLR, and LALR(1)), with support for
//! detecting and reporting parsing conflicts and ambiguities.

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
