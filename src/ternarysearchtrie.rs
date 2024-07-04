use pyo3::prelude::*;
use std::collections::HashMap;


#[pyclass]
/// A Ternary Search Trie data structure.
pub struct TernarySearchTrie {
    root: Option<Box<TSTNode>>,
}

struct TSTNode {
    c: char,
    left: Option<Box<TSTNode>>,
    middle: Option<Box<TSTNode>>,
    right: Option<Box<TSTNode>>,
    value: Option<String>,
}

impl TSTNode {
    fn new(c: char) -> Self {
        TSTNode {
            c,
            left: None,
            middle: None,
            right: None,
            value: None,
        }
    }
}

#[pymethods]
impl TernarySearchTrie {
    #[new]
    /// Create a new empty Ternary Search Trie.
    fn new() -> Self {
        TernarySearchTrie { root: None }
    }

    /// Insert a key-value pair into the trie.
    ///
    /// Args:
    ///     key (str): The key to insert.
    ///     value (str): The value associated with the key.
    fn insert(&mut self, key: &str, value: &str) {
        let mut tmproot = self.root.take();
        let new_root = self.insert_recursive(tmproot, key, value, 0);
        self.root = new_root;
    }

    /// Search for a key in the trie.
    ///
    /// Args:
    ///     key (str): The key to search for.
    ///
    /// Returns:
    ///     Optional[str]: The value associated with the key, or None if not found.
    fn search(&self, key: &str) -> Option<String> {
        self.search_recursive(&self.root, key, 0)
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
        if let Some(node) = self.find_node(&self.root, prefix, 0) {
            self.collect(node, &mut String::from(prefix), &mut results);
        }
        Ok(results)
    }
}

impl TernarySearchTrie {
    fn insert_recursive(
        &mut self,
        node: Option<Box<TSTNode>>,
        key: &str,
        value: &str,
        d: usize,
    ) -> Option<Box<TSTNode>> {
        let c = key.chars().nth(d).unwrap();
        let mut node = match node {
            Some(mut node) => {
                if c < node.c {
                    node.left = self.insert_recursive(node.left.take(), key, value, d);
                } else if c > node.c {
                    node.right = self.insert_recursive(node.right.take(), key, value, d);
                } else if d < key.len() - 1 {
                    node.middle = self.insert_recursive(node.middle.take(), key, value, d + 1);
                } else {
                    node.value = Some(String::from(value));
                }
                node
            }
            None => {
                let mut new_node = Box::new(TSTNode::new(c));
                if d < key.len() - 1 {
                    new_node.middle = self.insert_recursive(None, key, value, d + 1);
                } else {
                    new_node.value = Some(String::from(value));
                }
                new_node
            }
        };
        Some(node)
    }

    fn search_recursive(
        &self,
        node: &Option<Box<TSTNode>>,
        key: &str,
        d: usize,
    ) -> Option<String> {
        if let Some(node) = node {
            let c = key.chars().nth(d).unwrap();
            if c < node.c {
                return self.search_recursive(&node.left, key, d);
            } else if c > node.c {
                return self.search_recursive(&node.right, key, d);
            } else if d < key.len() - 1 {
                return self.search_recursive(&node.middle, key, d + 1);
            } else {
                return node.value.clone();
            }
        }
        None
    }

    fn find_node<'a>(
        &self,
        node: &'a Option<Box<TSTNode>>,
        key: &str,
        d: usize,
    ) -> Option<&'a Box<TSTNode>> {
        if let Some(node) = node {
            if d == key.len() {
                return Some(node);
            }
            let c = key.chars().nth(d).unwrap();
            if c < node.c {
                return self.find_node(&node.left, key, d);
            } else if c > node.c {
                return self.find_node(&node.right, key, d);
            } else {
                return self.find_node(&node.middle, key, d + 1);
            }
        }
        None
    }

    fn collect(&self, node: &Box<TSTNode>, prefix: &mut String, results: &mut HashMap<String, String>) {
        if let Some(value) = &node.value {
            results.insert(prefix.clone(), value.clone());
        }
        if let Some(left) = &node.left {
            self.collect(left, prefix, results);
        }
        if let Some(middle) = &node.middle {
            prefix.push(node.c);
            self.collect(middle, prefix, results);
            prefix.pop();
        }
        if let Some(right) = &node.right {
            self.collect(right, prefix, results);
        }
    }
}

