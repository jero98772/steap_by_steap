// src/unionfind.rs
use pyo3::prelude::*;

/// The Union-Find structure is used to efficiently manage and merge disjoint sets.
/// This module provides an implementation of the Union-Find (disjoint set) data structure.
#[pyclass]
pub struct UnionFind {
    /// The parent array, where parent[i] points to the parent of node i. If parent[i] == i, then i is a root.
    parent: Vec<usize>,
    /// The rank array, used to keep the tree flat by storing the depth of the tree for each node.

    rank: Vec<usize>,
}

#[pymethods]
impl UnionFind {

    /// Creates a new Union-Find data structure with `n` elements, each initially in its own set.
    ///
    /// # Arguments
    ///
    /// * `n` - The number of elements in the Union-Find data structure.
    ///
    /// # Example
    ///
    /// ```
    /// let uf = UnionFind::new(10);
    /// ```
    #[new]
    pub fn new(n: usize) -> Self {
        let mut parent = vec![0; n];
        let mut rank = vec![0; n];
        for i in 0..n {
            parent[i] = i;
        }
        UnionFind { parent, rank }
    }
    /// Finds the representative (root) of the set containing `x` using path compression.
    ///
    /// # Arguments
    ///
    /// * `x` - The element for which to find the set representative.
    ///
    /// # Returns
    ///
    /// The representative of the set containing `x`.
    ///
    /// # Example
    ///
    /// ```
    /// let root = uf.find(3);
    /// ```
    pub fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }
    /// Unites the sets containing `x` and `y`. Uses union by rank to keep the tree flat.
    ///
    /// # Arguments
    ///
    /// * `x` - An element in the first set.
    /// * `y` - An element in the second set.
    ///
    /// # Example
    ///
    /// ```
    /// uf.union(3, 4);
    /// ```
    pub fn union(&mut self, x: usize, y: usize) {
        let root_x = self.find(x);
        let root_y = self.find(y);

        if root_x == root_y {
            return;
        }

        if self.rank[root_x] < self.rank[root_y] {
            self.parent[root_x] = root_y;
        } else if self.rank[root_x] > self.rank[root_y] {
            self.parent[root_y] = root_x;
        } else {
            self.parent[root_y] = root_x;
            self.rank[root_x] += 1;
        }
    }
    /// Checks if `x` and `y` are in the same set.
    ///
    /// # Arguments
    ///
    /// * `x` - An element in the first set.
    /// * `y` - An element in the second set.
    ///
    /// # Returns
    ///
    /// `true` if `x` and `y` are in the same set, `false` otherwise.
    ///
    /// # Example
    ///
    /// ```
    /// let same = uf.same_set(3, 4);
    /// ```
    pub fn same_set(&mut self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }
}
