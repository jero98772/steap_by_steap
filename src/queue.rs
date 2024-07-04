use pyo3::prelude::*;

/// A queue data structure specifically for `f64` items.
#[pyclass]
pub struct QueueF64 {
    items: Vec<f64>,
}

#[pymethods]
impl QueueF64 {
    /// Creates a new, empty queue.

    #[new]
    fn new() -> Self {
        QueueF64 { items: Vec::new() }
    }
    /// Adds an item to the end of the queue.
    ///
    /// # Arguments
    ///
    /// * `item` - The item to be added to the queue.
    fn push(&mut self, item: f64) {
        self.items.push(item);
    }
    /// Removes and returns the item at the front of the queue, or `None` if the queue is empty.
    fn pop(&mut self) -> Option<f64> {
        if self.is_empty() {
            None
        } else {
            Some(self.items.remove(0))
        }

    }
    /// Returns a reference to the item at the front of the queue without removing it,
    /// or `None` if the queue is empty.
    fn peek(&self) -> Option<f64> {
        self.items.first().copied()
    }
    /// Returns `true` if the stack is empty, and `false` otherwise.
    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }


    /// Returns the number of items in the stack.
    fn size(&self) -> usize {
        self.items.len()
    }
    /// Prints the contents of the queue.
    fn print(&self) {
        println!("Queue: {:?}", self.items);
    }
    /// Returns the number of items in the queue.
    fn len(&self) -> usize {
        self.items.len()
    }
}

/// A queue data structure specifically for `i32` items.

#[pyclass]
pub struct QueueI32 {
    items: Vec<i32>,
}

#[pymethods]
impl QueueI32 {
    /// Creates a new, empty queue.

    #[new]
    fn new() -> Self {
        QueueI32 { items: Vec::new() }
    }
    /// Adds an item to the end of the queue.
    ///
    /// # Arguments
    ///
    /// * `item` - The item to be added to the queue.
    fn push(&mut self, item: i32) {
        self.items.push(item);
    }
    /// Removes and returns the item at the front of the queue, or `None` if the queue is empty.
    fn pop(&mut self) -> Option<i32> {
        if self.is_empty() {
            None
        } else {
            Some(self.items.remove(0))
        }

    }
    /// Returns a reference to the item at the front of the queue without removing it,
    /// or `None` if the queue is empty.
    fn peek(&self) -> Option<i32> {
        self.items.first().copied()
    }
    /// Returns `true` if the stack is empty, and `false` otherwise.
    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    
    /// Returns the number of items in the stack.
    fn size(&self) -> usize {
        self.items.len()
    }
    /// Prints the contents of the queue.
    fn print(&self) {
        println!("Queue: {:?}", self.items);
    }
    /// Returns the number of items in the queue.
    fn len(&self) -> usize {
        self.items.len()
    }
}
