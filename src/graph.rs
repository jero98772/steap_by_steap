use pyo3::prelude::*;
use std::collections::{HashMap, VecDeque, HashSet};

/// Represents a graph using an adjacency list.
#[pyclass]
pub struct Graph {
    adjacency_list: HashMap<String, Vec<String>>,
}

#[pymethods]
impl Graph {
    /// Create a new empty graph.
    #[new]
    fn new() -> Self {
        Graph {
            adjacency_list: HashMap::new(),
        }
    }

    /// Add an edge to the graph.
    ///
    /// # Arguments
    ///
    /// * `src` - A string slice that holds the source vertex.
    /// * `dst` - A string slice that holds the destination vertex.
    fn add_edge(&mut self, src: &str, dst: &str) {
        self.adjacency_list
            .entry(src.to_string())
            .or_insert_with(Vec::new)
            .push(dst.to_string());
        self.adjacency_list
            .entry(dst.to_string())
            .or_insert_with(Vec::new)
            .push(src.to_string());
    }

    /// Perform a Depth-First Search (DFS) starting from a given vertex.
    ///
    /// # Arguments
    ///
    /// * `start` - A string slice that holds the starting vertex.
    ///
    /// # Returns
    ///
    /// A list of vertices in the order they were visited.
    fn dfs(&self, start: &str) -> Vec<String> {
        let mut visited = HashSet::new();
        let mut stack = vec![start.to_string()];
        let mut result = vec![];

        while let Some(node) = stack.pop() {
            if !visited.contains(&node) {
                visited.insert(node.clone());
                result.push(node.clone());

                if let Some(neighbors) = self.adjacency_list.get(&node) {
                    for neighbor in neighbors {
                        if !visited.contains(neighbor) {
                            stack.push(neighbor.clone());
                        }
                    }
                }
            }
        }

        result
    }

    /// Perform a Breadth-First Search (BFS) starting from a given vertex.
    ///
    /// # Arguments
    ///
    /// * `start` - A string slice that holds the starting vertex.
    ///
    /// # Returns
    ///
    /// A list of vertices in the order they were visited.
    fn bfs(&self, start: &str) -> Vec<String> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        let mut result = vec![];

        visited.insert(start.to_string());
        queue.push_back(start.to_string());

        while let Some(node) = queue.pop_front() {
            result.push(node.clone());

            if let Some(neighbors) = self.adjacency_list.get(&node) {
                for neighbor in neighbors {
                    if !visited.contains(neighbor) {
                        visited.insert(neighbor.clone());
                        queue.push_back(neighbor.clone());
                    }
                }
            }
        }

        result
    }
}

/// Create a new graph instance.
#[pyfunction]
fn create_graph() -> Graph {
    Graph::new()
}
