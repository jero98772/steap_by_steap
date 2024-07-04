// src/stack.rs

use pyo3::prelude::*;
/// A stack data structure for `i32` that supports typical stack operations.
#[pyclass]
pub struct StackI32 {
    items: Vec<i32>,
}

#[pymethods]
impl StackI32 {
    /// Creates a new, empty stack.

    #[new]
    fn new() -> Self {
        StackI32 { items: Vec::new() }
    }
    /// Pushes an item onto the top of the stack.
    ///
    /// # Arguments
    ///
    /// * `item` - The item to be pushed onto the stack.
    fn push(&mut self, item: i32) {
        self.items.push(item);
    }
    /// Removes and returns the item at the top of the stack, or `None` if the stack is empty.
    fn pop(&mut self) -> Option<i32> {
        self.items.pop()
    }

    /// Returns a reference to the item at the top of the stack without removing it, or `None` if the stack is empty.
    fn peek(&self) -> Option<i32> {
        self.items.last().copied()
    }
    /// Returns `true` if the stack is empty, and `false` otherwise.
    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
    /// Returns the number of items in the stack.
    fn size(&self) -> usize {
        self.items.len()
    }
    /// Prints the contents of the stack.
    fn print(&self) {
        println!("Stack: {:?}", self.items);
    }
}

/// A stack data structure for `f64` that supports typical stack operations.
#[pyclass]
pub struct StackF64 {
    items: Vec<f64>,
}

#[pymethods]
impl StackF64 {
    /// Creates a new, empty stack.

    #[new]
    fn new() -> Self {
        StackF64 { items: Vec::new() }
    }
    /// Pushes an item onto the top of the stack.
    ///
    /// # Arguments
    ///
    /// * `item` - The item to be pushed onto the stack.
    fn push(&mut self, item: f64) {
        self.items.push(item);
    }
    /// Removes and returns the item at the top of the stack, or `None` if the stack is empty.
    fn pop(&mut self) -> Option<f64> {
        self.items.pop()
    }
    /// Returns a reference to the item at the top of the stack without removing it, or `None` if the stack is empty.
    fn peek(&self) -> Option<f64> {
        self.items.last().copied()
    }
    /// Returns `true` if the stack is empty, and `false` otherwise.
    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
    /// Returns the number of items in the stack.
    fn size(&self) -> usize {
        self.items.len()
    }
    /// Prints the contents of the stack.
    fn print(&self) {
        println!("Stack: {:?}", self.items);
    }

}
