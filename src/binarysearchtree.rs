use pyo3::prelude::*;

/// Represents a Node in a Binary Search Tree.
#[pyclass]
pub struct Node {
    /// The value stored in the node.
    value: i32,
    /// The left child node.
    left: Option<Box<Node>>,
    /// The right child node.
    right: Option<Box<Node>>,
}

#[pymethods]
impl Node {
    /// Creates a new Node with the given value.
    #[new]
    fn new(value: i32) -> Self {
        Node {
            value,
            left: None,
            right: None,
        }
    }

    /// Inserts a value into the Binary Search Tree.
    ///
    /// If the value is less than the current node's value, it goes to the left;
    /// otherwise, it goes to the right.
    fn insert(&mut self, value: i32) {
        if value < self.value {
            match &mut self.left {
                Some(node) => node.insert(value),
                None => self.left = Some(Box::new(Node::new(value))),
            }
        } else {
            match &mut self.right {
                Some(node) => node.insert(value),
                None => self.right = Some(Box::new(Node::new(value))),
            }
        }
    }

    /// Searches for a value in the Binary Search Tree.
    ///
    /// Returns true if the value is found in the tree; otherwise, false.
    fn search(&self, value: i32) -> bool {
        if value == self.value {
            true
        } else if value < self.value {
            match &self.left {
                Some(node) => node.search(value),
                None => false,
            }
        } else {
            match &self.right {
                Some(node) => node.search(value),
                None => false,
            }
        }
    }
}

/// Represents a Binary Search Tree (BST).
#[pyclass]
pub struct BinarySearchTree {
    root: Option<Box<Node>>,
}

#[pymethods]
impl BinarySearchTree {
    /// Creates a new empty Binary Search Tree (BST).
    #[new]
    fn new() -> Self {
        BinarySearchTree {
            root: None,
        }
    }

    /// Inserts a value into the Binary Search Tree (BST).
    ///
    /// If the tree is empty, creates a new root node with the given value.
    /// Otherwise, recursively inserts the value into the appropriate position.
    fn insert(&mut self, value: i32) {
        if let Some(ref mut root) = self.root {
            root.insert(value);
        } else {
            self.root = Some(Box::new(Node::new(value)));
        }
    }

    /// Searches for a value in the Binary Search Tree (BST).
    ///
    /// Returns true if the value is found in the tree; otherwise, false.
    ///
    /// If the tree is empty, returns false.
    fn search(&self, value: i32) -> bool {
        if let Some(ref root) = self.root {
            root.search(value)
        } else {
            false
        }
    }
}
