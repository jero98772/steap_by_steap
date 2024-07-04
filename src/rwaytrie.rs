use pyo3::prelude::*;
use std::collections::HashMap;

#[pyclass]
/// An R-way Trie data structure.
pub struct RWayTrie {
    root: Option<Box<Node>>,
}

struct Node {
    value: Option<String>,
    children: HashMap<u8, Box<Node>>,
}

impl Node {
    fn new() -> Self {
        Node {
            value: None,
            children: HashMap::new(),
        }
    }
}

#[pymethods]
impl RWayTrie {
    #[new]
    /// Create a new empty R-way Trie.
    fn new() -> Self {
        RWayTrie { root: None }
    }

    /// Insert a key-value pair into the trie.
    ///
    /// Args:
    ///     key (str): The key to insert.
    ///     value (str): The value associated with the key.
    fn insert(&mut self, key: &str, value: &str) {
        if self.root.is_none() {
            self.root = Some(Box::new(Node::new()));
        }
        let mut current = self.root.as_mut().unwrap();
        for &byte in key.as_bytes() {
            current = current.children.entry(byte).or_insert_with(|| Box::new(Node::new()));
        }
        current.value = Some(value.to_string());
    }

    /// Search for a key in the trie.
    ///
    /// Args:
    ///     key (str): The key to search for.
    ///
    /// Returns:
    ///     Optional[str]: The value associated with the key, or None if not found.
    fn search(&self, key: &str) -> Option<String> {
        let mut current = self.root.as_ref()?;
        for &byte in key.as_bytes() {
            current = current.children.get(&byte)?;
        }
        current.value.clone()
    }
    /// Get all key-value pairs in the trie with a given prefix.
    ///
    /// Args:
    ///     prefix (str): The prefix to search for.
    ///
    /// Returns:
    ///     Dict[str, str]: A dictionary of key-value pairs with the given prefix.
    fn keys_with_prefix(&self, prefix: &str) -> PyResult<HashMap<String, String>> {
        let mut results = HashMap::new();
        let mut current = self.root.as_deref();
        for &byte in prefix.as_bytes() {
            match current {
                Some(node) => current = node.children.get(&byte).map(|boxed_node| boxed_node.as_ref()),
                None => return Ok(results),
            }
        }
        if let Some(node) = current {
            self.collect(node, &mut String::from(prefix), &mut results);
        }
        Ok(results)
    }
}

impl RWayTrie {
    fn collect(&self, node: &Node, prefix: &mut String, results: &mut HashMap<String, String>) {
        if let Some(value) = &node.value {
            results.insert(prefix.clone(), value.clone());
        }
        for (&byte, child) in &node.children {
            prefix.push(byte as char);
            self.collect(child, prefix, results);
            prefix.pop();
        }
    }
}