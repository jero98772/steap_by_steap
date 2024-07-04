use pyo3::prelude::*;
use std::collections::{BinaryHeap, HashMap, HashSet,VecDeque};
use std::cmp::Ordering;
use std::cmp::min;

#[pyclass]
pub struct WeightedGraph {
    adjacency_list: HashMap<i32, Vec<(i32, i32)>>,
}

#[derive(Copy, Clone, Eq, PartialEq)]
struct State {
    cost: i32,
    node: i32,
}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        other.cost.cmp(&self.cost)
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[pymethods]
impl WeightedGraph {
    #[new]
    fn new() -> Self {
        WeightedGraph {
            adjacency_list: HashMap::new(),
        }
    }

    /// Add an edge to the graph
    ///
    /// Args:
    ///     from_node (int): The source node
    ///     to_node (int): The destination node
    ///     weight (int): The weight of the edge
    fn add_edge(&mut self, from_node: i32, to_node: i32, weight: i32) {
        self.adjacency_list
            .entry(from_node)
            .or_insert(Vec::new())
            .push((to_node, weight));
    }

    /// Find the shortest path using Dijkstra's algorithm
    ///
    /// Args:
    ///     start (int): The starting node
    ///     end (int): The ending node
    ///
    /// Returns:
    ///     tuple: A tuple containing the total cost and the path (as a list of nodes)
    fn dijkstra(&self, start: i32, end: i32) -> PyResult<(i32, Vec<i32>)> {
        let mut distances: HashMap<i32, i32> = HashMap::new();
        let mut heap = BinaryHeap::new();
        let mut previous: HashMap<i32, i32> = HashMap::new();

        distances.insert(start, 0);
        heap.push(State { cost: 0, node: start });

        while let Some(State { cost, node }) = heap.pop() {
            if node == end {
                let mut path = vec![end];
                let mut current = end;
                while let Some(&prev) = previous.get(&current) {
                    path.push(prev);
                    current = prev;
                }
                path.reverse();
                return Ok((cost, path));
            }

            if cost > *distances.get(&node).unwrap_or(&i32::MAX) {
                continue;
            }

            if let Some(neighbors) = self.adjacency_list.get(&node) {
                for &(next_node, weight) in neighbors {
                    let next_cost = cost + weight;
                    if next_cost < *distances.get(&next_node).unwrap_or(&i32::MAX) {
                        distances.insert(next_node, next_cost);
                        previous.insert(next_node, node);
                        heap.push(State { cost: next_cost, node: next_node });
                    }
                }
            }
        }

        Err(PyErr::new::<pyo3::exceptions::PyValueError, _>("No path found"))
    }

    /// Find the shortest path using Bellman-Ford algorithm
    ///
    /// Args:
    ///     start (int): The starting node
    ///     end (int): The ending node
    ///
    /// Returns:
    ///     tuple: A tuple containing the total cost and the path (as a list of nodes)
    fn bellman_ford(&self, start: i32, end: i32) -> PyResult<(i32, Vec<i32>)> {
        let mut distances: HashMap<i32, i32> = HashMap::new();
        let mut previous: HashMap<i32, i32> = HashMap::new();

        for &node in self.adjacency_list.keys() {
            distances.insert(node, i32::MAX);
        }
        distances.insert(start, 0);

        let node_count = self.adjacency_list.len();

        for _ in 0..node_count - 1 {
            for (&node, edges) in &self.adjacency_list {
                for &(neighbor, weight) in edges {
                    let dist = *distances.get(&node).unwrap_or(&i32::MAX);
                    if dist == i32::MAX {
                        continue;
                    }
                    let new_dist = dist + weight;
                    if new_dist < *distances.get(&neighbor).unwrap_or(&i32::MAX) {
                        distances.insert(neighbor, new_dist);
                        previous.insert(neighbor, node);
                    }
                }
            }
        }

        // Check for negative weight cycles
        for (&node, edges) in &self.adjacency_list {
            for &(neighbor, weight) in edges {
                let dist = *distances.get(&node).unwrap_or(&i32::MAX);
                if dist == i32::MAX {
                    continue;
                }
                if dist + weight < *distances.get(&neighbor).unwrap_or(&i32::MAX) {
                    return Err(PyErr::new::<pyo3::exceptions::PyValueError, _>("Graph contains a negative weight cycle"));
                }
            }
        }

        let mut path = vec![end];
        let mut current = end;
        while let Some(&prev) = previous.get(&current) {
            path.push(prev);
            current = prev;
        }
        path.reverse();

        if path[0] != start {
            return Err(PyErr::new::<pyo3::exceptions::PyValueError, _>("No path found"));
        }

        Ok((*distances.get(&end).unwrap(), path))
    }
    // ... (previous methods for dijkstra and bellman_ford remain unchanged)

    /// Find the Minimum Spanning Tree using Prim's algorithm
    ///
    /// Returns:
    ///     list: A list of tuples representing the edges in the MST (from_node, to_node, weight)
    fn prim(&self) -> PyResult<Vec<(i32, i32, i32)>> {
        let mut mst = Vec::new();
        let mut visited = HashSet::new();
        let mut heap = BinaryHeap::new();

        if let Some(&start_node) = self.adjacency_list.keys().next() {
            visited.insert(start_node);
            for &(neighbor, weight) in &self.adjacency_list[&start_node] {
                heap.push(State { cost: -weight, node: neighbor });
            }

            while let Some(State { cost, node }) = heap.pop() {
                if visited.insert(node) {
                    if let Some(parent) = self.adjacency_list[&node].iter()
                        .find(|&&(n, _)| visited.contains(&n))
                        .map(|&(n, _)| n) {
                        mst.push((parent, node, -cost));
                    }

                    for &(neighbor, weight) in &self.adjacency_list[&node] {
                        if !visited.contains(&neighbor) {
                            heap.push(State { cost: -weight, node: neighbor });
                        }
                    }
                }
            }
        }

        Ok(mst)
    }

    /// Find the Minimum Spanning Tree using Kruskal's algorithm
    ///
    /// Returns:
    ///     list: A list of tuples representing the edges in the MST (from_node, to_node, weight)
    fn kruskal(&self) -> PyResult<Vec<(i32, i32, i32)>> {
        struct DisjointSet {
            parent: HashMap<i32, i32>,
            rank: HashMap<i32, i32>,
        }

        impl DisjointSet {
            fn new() -> Self {
                DisjointSet {
                    parent: HashMap::new(),
                    rank: HashMap::new(),
                }
            }

            fn make_set(&mut self, v: i32) {
                self.parent.entry(v).or_insert(v);
                self.rank.entry(v).or_insert(0);
            }

    fn find(&mut self, v: i32) -> i32 {
        let mut current = v;
        while self.parent[&current] != current {
            let next = self.parent[&current];
            self.parent.insert(current, self.parent[&next]);
            current = next;
        }
        current
    }
            fn union(&mut self, x: i32, y: i32) {
                let x_root = self.find(x);
                let y_root = self.find(y);

                if x_root == y_root {
                    return;
                }

                let x_rank = self.rank[&x_root];
                let y_rank = self.rank[&y_root];

                if x_rank < y_rank {
                    self.parent.insert(x_root, y_root);
                } else if x_rank > y_rank {
                    self.parent.insert(y_root, x_root);
                } else {
                    self.parent.insert(y_root, x_root);
                    self.rank.insert(x_root, x_rank + 1);
                }
            }
        }

        let mut edges = Vec::new();
        for (&u, neighbors) in &self.adjacency_list {
            for &(v, weight) in neighbors {
                if u < v {
                    edges.push((u, v, weight));
                }
            }
        }
        edges.sort_by_key(|&(_, _, w)| w);

        let mut disjoint_set = DisjointSet::new();
        for &node in self.adjacency_list.keys() {
            disjoint_set.make_set(node);
        }

        let mut mst = Vec::new();
        for (u, v, weight) in edges {
            if disjoint_set.find(u) != disjoint_set.find(v) {
                disjoint_set.union(u, v);
                mst.push((u, v, weight));
            }
        }

        Ok(mst)
    }


    /// Find the maximum flow using Ford-Fulkerson algorithm
    ///
    /// Args:
    ///     source (int): The source node
    ///     sink (int): The sink node
    ///
    /// Returns:
    ///     int: The maximum flow from source to sink
    fn ford_fulkerson(&mut self, source: i32, sink: i32) -> PyResult<i32> {
        let mut max_flow = 0;

        loop {
            let (path, flow) = self.bfs_find_path(source, sink);
            if flow == 0 {
                break;
            }

            max_flow += flow;

            let mut current = sink;
            for &prev in path.iter().rev() {
                if let Some(edge) = self.adjacency_list.get_mut(&prev).unwrap().iter_mut().find(|e| e.0 == current) {
                    edge.1 -= flow;
                }
                if let Some(edge) = self.adjacency_list.get_mut(&current).unwrap().iter_mut().find(|e| e.0 == prev) {
                    edge.1 += flow;
                }
                current = prev;
            }
        }

        Ok(max_flow)
    }

    fn bfs_find_path(&self, source: i32, sink: i32) -> (Vec<i32>, i32) {
        let mut queue = VecDeque::new();
        let mut visited = HashSet::new();
        let mut parent = HashMap::new();
        let mut path_flow = HashMap::new();

        queue.push_back(source);
        visited.insert(source);
        path_flow.insert(source, i32::MAX);

        while let Some(current) = queue.pop_front() {
            if current == sink {
                break;
            }

            if let Some(neighbors) = self.adjacency_list.get(&current) {
                for &(next, capacity) in neighbors {
                    if !visited.contains(&next) && capacity > 0 {
                        visited.insert(next);
                        parent.insert(next, current);
                        path_flow.insert(next, min(path_flow[&current], capacity));
                        queue.push_back(next);
                    }
                }
            }
        }

        if !visited.contains(&sink) {
            return (Vec::new(), 0);
        }

        let mut path = Vec::new();
        let mut current = sink;
        while current != source {
            path.push(current);
            current = parent[&current];
        }
        path.push(source);
        path.reverse();

        (path, path_flow[&sink])
    }
}