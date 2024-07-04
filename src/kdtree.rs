use pyo3::prelude::*;
use std::cmp::Ordering;

#[pyclass]
#[derive(Debug)]
struct Point {
    coords: Vec<f64>,
}

#[pymethods]
impl Point {
    #[new]
    fn new(coords: Vec<f64>) -> Self {
        Point { coords }
    }
}

/// A node in the KDTree
#[derive(Debug)]
struct Node {
    point: Vec<f64>,
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
}

impl Node {
    fn new(point: Vec<f64>) -> Self {
        Node {
            point,
            left: None,
            right: None,
        }
    }
}

/// KDTree implementation for organizing points in an N-dimensional space
#[pyclass]
#[derive(Debug)]
pub struct KdTree {
    root: Option<Box<Node>>,
    dimensions: usize,
}

#[pymethods]
impl KdTree {
    /// Create a new KDTree with a given number of dimensions
    ///
    /// # Arguments
    ///
    /// * `dimensions` - The number of dimensions for the KDTree
    #[new]
    pub fn new(dimensions: usize) -> Self {
        KdTree {
            root: None,
            dimensions,
        }
    }

    /// Insert a point into the KDTree
    ///
    /// # Arguments
    ///
    /// * `point` - The point to insert into the KDTree
    pub fn insert(&mut self, point: Vec<f64>) {
        let root = self.root.take();
        self.root = self.insert_recursive(root, point, 0);
    }
}

impl KdTree {
    fn insert_recursive(&mut self, node: Option<Box<Node>>, point: Vec<f64>, depth: usize) -> Option<Box<Node>> {
        match node {
            Some(mut n) => {
                let dim = depth % self.dimensions;
                let ordering = point[dim].partial_cmp(&n.point[dim]);

                match ordering {
                    Some(Ordering::Less) | Some(Ordering::Equal) => {
                        n.left = self.insert_recursive(n.left.take(), point, depth + 1);
                    }
                    Some(Ordering::Greater) => {
                        n.right = self.insert_recursive(n.right.take(), point, depth + 1);
                    }
                    None => {
                        // Handle NaNs or other unordered comparisons
                        panic!("NaNs or unordered comparison encountered!");
                    }
                }

                Some(n)
            }
            None => Some(Box::new(Node::new(point))),
        }
    }
}


