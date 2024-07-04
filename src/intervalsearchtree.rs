use pyo3::prelude::*;
use pyo3::wrap_pyfunction;

/// Represents an interval with a start and end point.
#[pyclass]
#[derive(Clone, Debug)]
pub struct Interval {
    #[pyo3(get, set)]
    start: i32,
    #[pyo3(get, set)]
    end: i32,
}

#[pymethods]
impl Interval {
    /// Creates a new interval with the given start and end points.
    #[new]
    fn new(start: i32, end: i32) -> Self {
        Interval { start, end }
    }

    fn __repr__(&self) -> String {
        format!("Interval({}, {})", self.start, self.end)
    }
}
#[derive(Debug)]
struct Node {
    interval: Interval,
    max: i32,
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
}

impl Node {
    fn new(interval: Interval) -> Self {
        let max = interval.end;
        Node {
            interval,
            max,
            left: None,
            right: None,
        }
    }
}

/// Represents an interval search tree.
#[pyclass]
pub struct IntervalTree {
    root: Option<Box<Node>>,
}

impl IntervalTree {
    fn insert_rec(node: Option<Box<Node>>, interval: &Interval) -> Box<Node> {
        if let Some(mut node) = node {
            if interval.start < node.interval.start {
                node.left = Some(Self::insert_rec(node.left.take(), interval));
            } else {
                node.right = Some(Self::insert_rec(node.right.take(), interval));
            }
            node.max = node.max.max(interval.end);
            node
        } else {
            Box::new(Node::new(interval.clone()))
        }
    }

    fn search_rec(node: &Option<Box<Node>>, interval: &Interval, result: &mut Vec<Interval>) {
        if let Some(node) = node {
            if node.interval.start <= interval.end && interval.start <= node.interval.end {
                result.push(node.interval.clone());
            }
            if let Some(left) = &node.left {
                if left.max >= interval.start {
                    Self::search_rec(&node.left, interval, result);
                }
            }
            Self::search_rec(&node.right, interval, result);
        }
    }
}


#[pymethods]
impl IntervalTree {
    /// Creates a new empty interval tree.
    #[new]
    fn new() -> Self {
        IntervalTree { root: None }
    }

    /// Inserts an interval into the interval tree.
    ///
    /// # Arguments
    ///
    /// * `interval` - An Interval object to insert.
    fn insert(&mut self, start:i32, end:i32) {

        self.root = Some(Self::insert_rec(self.root.take(), &Interval::new(start, end)));
    }

    /// Searches for intervals that overlap with the given interval.
    ///
    /// # Arguments
    ///
    /// * `interval` - An Interval object to search for overlaps.
    ///
    /// # Returns
    ///
    /// A list of intervals that overlap with the given interval.
    fn search(&self, start:i32, end:i32) -> Vec<Interval> {
        let mut result = Vec::new();
        Self::search_rec(&self.root, &Interval::new(start, end), &mut result);
        result
    }
}


