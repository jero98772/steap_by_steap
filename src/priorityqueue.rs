use std::cmp::Reverse;
use std::collections::BinaryHeap;
use pyo3::prelude::*;

/// A priority queue implemented using a binary heap.
#[pyclass]
pub struct PriorityQueue {
    heap: BinaryHeap<Reverse<i32>>,
}

#[pymethods]
impl PriorityQueue {
    /// Creates a new empty `PriorityQueue`.
    ///
    /// # Returns
    ///
    /// A new instance of `PriorityQueue`.
    #[new]
    fn new() -> Self {
        PriorityQueue {
            heap: BinaryHeap::new(),
        }
    }

    /// Adds an element to the priority queue.
    ///
    /// # Arguments
    ///
    /// * `value` - The integer value to be added to the queue.
    fn push(&mut self, value: i32) {
        self.heap.push(Reverse(value));
    }

    /// Removes and returns the smallest element from the priority queue.
    ///
    /// # Returns
    ///
    /// An `Option<i32>` containing the smallest element, or `None` if the queue is empty.
    fn pop(&mut self) -> Option<i32> {
        self.heap.pop().map(|Reverse(value)| value)
    }

    /// Returns a reference to the smallest element in the priority queue without removing it.
    ///
    /// # Returns
    ///
    /// An `Option<i32>` containing a reference to the smallest element, or `None` if the queue is empty.
    fn peek(&self) -> Option<i32> {
        self.heap.peek().map(|Reverse(value)| *value)
    }

    /// Returns the number of elements in the priority queue.
    ///
    /// # Returns
    ///
    /// The number of elements in the queue as a `usize`.
    fn len(&self) -> usize {
        self.heap.len()
    }

    /// Checks if the priority queue is empty.
    ///
    /// # Returns
    ///
    /// `true` if the queue is empty, `false` otherwise.
    fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }
}



