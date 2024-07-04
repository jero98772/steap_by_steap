use std::collections::{HashMap, HashSet};
use pyo3::prelude::*;
use pyo3::wrap_pyfunction;
use pyo3::types::PyString;

#[pyclass]
#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct State {
    id: usize,
}

#[pymethods]
impl State {
    /// Creates a new State with the given ID.
    /// 
    /// # Arguments
    ///
    /// * `id` - A unique identifier for the state.
    #[new]
    fn new(id: usize) -> Self {
        State { id }
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum SymbolLocal {
    Epsilon, // Represent ε (epsilon) for non-deterministic transitions
    Char(char),
}

#[pyclass]
pub struct Symbol {
    symbol: SymbolLocal,
}

#[pymethods]
impl Symbol {
    /// Creates a new Symbol representing ε (epsilon).
    #[staticmethod]
    fn epsilon() -> Self {
        Symbol {
            symbol: SymbolLocal::Epsilon,
        }
    }
    /// Creates a new Symbol representing a character.
    ///
    /// # Arguments
    ///
    /// * `c` - The character to be represented by the symbol.
    #[staticmethod]
    fn char(c: char) -> Self {
        Symbol {
            symbol: SymbolLocal::Char(c),
        }
    }

    fn __repr__(&self) -> String {
        match self.symbol {
            SymbolLocal::Epsilon => "Epsilon".to_string(),
            SymbolLocal::Char(c) => format!("Char({})", c),
        }
    }
}

#[pyclass]
#[derive(Debug)]
pub struct NFA {
    states: HashSet<State>,
    alphabet: HashSet<SymbolLocal>,
    transitions: HashMap<State, Vec<(SymbolLocal, State)>>,
    start_state: State,
    accept_states: HashSet<State>,
}

#[pymethods]
impl NFA {
    /// Creates a new NFA with the given start state and accept states.
    ///
    /// # Arguments
    ///
    /// * `start_state` - The initial state of the NFA.
    /// * `accept_states` - A list of accept states for the NFA.

    #[new]
    fn new(start_state: State, accept_states: Vec<State>) -> Self {
        NFA {
            states: HashSet::new(),
            alphabet: HashSet::new(),
            transitions: HashMap::new(),
            start_state,
            accept_states: accept_states.into_iter().collect(),
        }
    }
    /// Adds a state to the NFA.
    ///
    /// # Arguments
    ///
    /// * `state` - The state to be added.
    fn add_state(&mut self, state: State) {
        self.states.insert(state);
    }
    /// Adds a transition to the NFA.
    ///
    /// # Arguments
    ///
    /// * `from` - The state from which the transition starts.
    /// * `py_symbol` - The symbol that triggers the transition.
    /// * `to` - The state to which the transition goes.
    fn add_transition(&mut self, from: State, py_symbol: &Symbol, to: State) {
        let symbol = py_symbol.symbol.clone();
        self.alphabet.insert(symbol.clone());
        self.transitions.entry(from).or_insert_with(Vec::new).push((symbol, to));
    }
    /// Computes the epsilon closure of a set of states.
    ///
    /// # Arguments
    ///
    /// * `states` - A list of states for which the epsilon closure is to be computed.
    ///
    /// # Returns
    ///
    /// A list of states that form the epsilon closure.

    fn epsilon_closure(&self, states: Vec<State>) -> Vec<State> {
        let mut closure: HashSet<State> = states.into_iter().collect();
        let mut stack: Vec<State> = closure.iter().cloned().collect();

        while let Some(state) = stack.pop() {
            if let Some(transitions) = self.transitions.get(&state) {
                for (symbol, next_state) in transitions {
                    if *symbol == SymbolLocal::Epsilon && !closure.contains(next_state) {
                        closure.insert(next_state.clone());
                        stack.push(next_state.clone());
                    }
                }
            }
        }

        closure.into_iter().collect()
    }
    /// Computes the set of states reachable from a set of states on a given symbol.
    ///
    /// # Arguments
    ///
    /// * `states` - A list of states from which the transitions are to be computed.
    /// * `py_symbol` - The symbol that triggers the transitions.
    ///
    /// # Returns
    ///
    /// A list of states reachable from the given states on the given symbol.

    fn move_states(&self, states: Vec<State>, py_symbol: &Symbol) -> Vec<State> {
        let symbol = &py_symbol.symbol;
        let mut next_states = HashSet::new();
        for state in states {
            if let Some(transitions) = self.transitions.get(&state) {
                for (trans_symbol, next_state) in transitions {
                    if trans_symbol == symbol {
                        next_states.insert(next_state.clone());
                    }
                }
            }
        }
        next_states.into_iter().collect()
    }
    /// Checks if the NFA accepts the given input string.
    ///
    /// # Arguments
    ///
    /// * `input` - The input string to be checked.
    ///
    /// # Returns
    ///
    /// A boolean indicating whether the input string is accepted by the NFA.

    fn is_accepted(&self, input: &PyString) -> bool {
        let input: &str = input.to_str().unwrap();
        let mut current_states = HashSet::new();
        current_states.insert(self.start_state.clone());
        let mut current_states_vec: Vec<State> = current_states.into_iter().collect();
        current_states_vec = self.epsilon_closure(current_states_vec);

        for c in input.chars() {
            let symbol = SymbolLocal::Char(c);
            let py_symbol = Symbol { symbol };
            current_states_vec = self.move_states(current_states_vec, &py_symbol);
            current_states_vec = self.epsilon_closure(current_states_vec);
        }

        for state in current_states_vec {
            if self.accept_states.contains(&state) {
                return true;
            }
        }
        false
    }
}

#[pymodule]
fn my_nfa(py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<State>()?;
    m.add_class::<Symbol>()?;
    m.add_class::<NFA>()?;
    Ok(())
}
