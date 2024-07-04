use pyo3::prelude::*;

/// A heap data structure implemented in Rust and exposed to Python.
#[pyclass]
pub struct Heap {
    data: Vec<i32>,
}

#[pymethods]
impl Heap {
    /// Creates a new empty Heap.
    #[new]
    fn new() -> Self {
        Heap { data: Vec::new() }
    }

    /// Pushes a value onto the heap.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to be added to the heap.
    fn push(&mut self, value: i32) {
        self.data.push(value);
        self.sift_up();
    }

    /// Pops the maximum value off the heap.
    ///
    /// Returns `Some(i32)` if the heap is not empty, otherwise returns `None`.
    fn pop(&mut self) -> Option<i32> {
        if self.data.is_empty() {
            return None;
        }
        let result = self.data.swap_remove(0);
        self.sift_down();
        Some(result)
    }

    /// Converts a vector into a heap.
    ///
    /// # Arguments
    ///
    /// * `data` - A vector of integers to be heapified.
    fn heapify(&mut self, data: Vec<i32>) {
        self.data = data;
        for i in (0..self.data.len() / 2).rev() {
            self.sift_down_from(i);
        }
    }

    /// Sorts the heap and returns a sorted vector.
    ///
    /// This consumes the heap.
    fn heapsort(&mut self) -> Vec<i32> {
        let mut sorted = Vec::new();
        while let Some(value) = self.pop() {
            sorted.push(value);
        }
        sorted
    }

    /// Returns the heap as a list.
    fn as_list(&self) -> Vec<i32> {
        self.data.clone()
    }

    /// Moves the last element up to maintain heap property.
    fn sift_up(&mut self) {
        let mut idx = self.data.len() - 1;
        while idx > 0 {
            let parent_idx = (idx - 1) / 2;
            if self.data[idx] <= self.data[parent_idx] {
                break;
            }
            self.data.swap(idx, parent_idx);
            idx = parent_idx;
        }
    }

    /// Moves the root element down to maintain heap property.
    fn sift_down(&mut self) {
        self.sift_down_from(0);
    }

    /// Sifts down the element at the given index to maintain heap property.
    ///
    /// # Arguments
    ///
    /// * `idx` - The index of the element to sift down.
    fn sift_down_from(&mut self, mut idx: usize) {
        let len = self.data.len();
        loop {
            let left = 2 * idx + 1;
            let right = 2 * idx + 2;
            let mut largest = idx;

            if left < len && self.data[left] > self.data[largest] {
                largest = left;
            }
            if right < len && self.data[right] > self.data[largest] {
                largest = right;
            }
            if largest == idx {
                break;
            }
            self.data.swap(idx, largest);
            idx = largest;
        }
    }
}

/// Heap sorts a vector of integers.
///
/// # Arguments
///
/// * `data` - A vector of integers to be sorted.
///
/// Returns a new vector with the integers sorted in descending order.
#[pyfunction]
pub fn Heapsort(data: Vec<i32>) -> Vec<i32> {
    let mut heap = Heap::new();
    heap.heapify(data);
    heap.heapsort()
}

