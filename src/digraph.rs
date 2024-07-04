use pyo3::prelude::*;
use std::collections::{HashMap, HashSet, VecDeque};

#[pyclass]
pub struct Digraph {
    adj_list: HashMap<usize, Vec<usize>>,
}

#[pymethods]
impl Digraph {
    #[new]
    fn new() -> Self {
        Digraph {
            adj_list: HashMap::new(),
        }
    }

    /// Add an edge from node u to node v.
    ///
    /// Parameters:
    /// u (int): The start node.
    /// v (int): The end node.
    fn add_edge(&mut self, u: usize, v: usize) {
        self.adj_list.entry(u).or_insert_with(Vec::new).push(v);
    }

    /// Perform Depth-First Search (DFS) starting from a node.
    ///
    /// Parameters:
    /// start (int): The start node.
    ///
    /// Returns:
    /// List[int]: The nodes visited in DFS order.
    fn dfs(&self, start: usize) -> Vec<usize> {
        let mut visited = HashSet::new();
        let mut stack = vec![start];
        let mut result = Vec::new();

        while let Some(node) = stack.pop() {
            if !visited.contains(&node) {
                visited.insert(node);
                result.push(node);
                if let Some(neighbors) = self.adj_list.get(&node) {
                    for &neighbor in neighbors.iter().rev() {
                        stack.push(neighbor);
                    }
                }
            }
        }

        result
    }

    /// Perform Breadth-First Search (BFS) starting from a node.
    ///
    /// Parameters:
    /// start (int): The start node.
    ///
    /// Returns:
    /// List[int]: The nodes visited in BFS order.
    fn bfs(&self, start: usize) -> Vec<usize> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        let mut result = Vec::new();

        queue.push_back(start);

        while let Some(node) = queue.pop_front() {
            if !visited.contains(&node) {
                visited.insert(node);
                result.push(node);
                if let Some(neighbors) = self.adj_list.get(&node) {
                    for &neighbor in neighbors {
                        queue.push_back(neighbor);
                    }
                }
            }
        }

        result
    }

    /// Perform topological sort on the graph.
    ///
    /// Returns:
    /// List[int]: The nodes in topological order.
    fn topological_sort(&self) -> Vec<usize> {
        let mut visited = HashSet::new();
        let mut stack = Vec::new();

        for &node in self.adj_list.keys() {
            if !visited.contains(&node) {
                self.topological_sort_util(node, &mut visited, &mut stack);
            }
        }

        stack.reverse();
        stack
    }

    /// Perform Kosaraju-Sharir algorithm to find strongly connected components.
    ///
    /// Returns:
    /// List[List[int]]: A list of strongly connected components.
    fn kosaraju_sharir(&self) -> Vec<Vec<usize>> {
        let mut visited = HashSet::new();
        let mut stack = Vec::new();

        for &node in self.adj_list.keys() {
            if !visited.contains(&node) {
                self.fill_order(node, &mut visited, &mut stack);
            }
        }

        let transposed = self.transpose();

        visited.clear();
        let mut scc = Vec::new();

        while let Some(node) = stack.pop() {
            if !visited.contains(&node) {
                let mut component = Vec::new();
                transposed.dfs_util(node, &mut visited, &mut component);
                scc.push(component);
            }
        }

        scc
    }
}

impl Digraph {
    fn topological_sort_util(&self, node: usize, visited: &mut HashSet<usize>, stack: &mut Vec<usize>) {
        visited.insert(node);
        if let Some(neighbors) = self.adj_list.get(&node) {
            for &neighbor in neighbors {
                if !visited.contains(&neighbor) {
                    self.topological_sort_util(neighbor, visited, stack);
                }
            }
        }
        stack.push(node);
    }

    fn fill_order(&self, node: usize, visited: &mut HashSet<usize>, stack: &mut Vec<usize>) {
        visited.insert(node);
        if let Some(neighbors) = self.adj_list.get(&node) {
            for &neighbor in neighbors {
                if !visited.contains(&neighbor) {
                    self.fill_order(neighbor, visited, stack);
                }
            }
        }
        stack.push(node);
    }

    fn transpose(&self) -> Digraph {
        let mut transposed = Digraph::new();

        for (&node, neighbors) in &self.adj_list {
            for &neighbor in neighbors {
                transposed.add_edge(neighbor, node);
            }
        }

        transposed
    }

    fn dfs_util(&self, node: usize, visited: &mut HashSet<usize>, component: &mut Vec<usize>) {
        visited.insert(node);
        component.push(node);
        if let Some(neighbors) = self.adj_list.get(&node) {
            for &neighbor in neighbors {
                if !visited.contains(&neighbor) {
                    self.dfs_util(neighbor, visited, component);
                }
            }
        }
    }
}

#[pymodule]
fn digraph(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<Digraph>()?;
    Ok(())
}
