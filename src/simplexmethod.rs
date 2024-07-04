use pyo3::prelude::*;
use ndarray::{Array1, Array2, s};

/// A struct representing a linear programming problem to be solved using the Simplex method.
#[pyclass]
pub struct Simplex {
    tableau: Array2<f64>,
}

#[pymethods]
impl Simplex {
    /// Create a new Simplex object with the given tableau.
    ///
    /// # Arguments
    ///
    /// * `tableau` - A 2D array representing the Simplex tableau.
    ///
    /// # Returns
    ///
    /// A new Simplex object.
    #[new]
    fn new(tableau: Vec<Vec<f64>>) -> Self {
        let rows = tableau.len();
        let cols = tableau[0].len();
        let flat_tableau: Vec<f64> = tableau.into_iter().flatten().collect();
        Simplex {
            tableau: Array2::from_shape_vec((rows, cols), flat_tableau).unwrap(),
        }
    }

    /// Perform the Simplex method on the given tableau.
    ///
    /// # Returns
    ///
    /// A vector containing the optimal solution.
    pub fn solve(&mut self) -> Vec<f64> {
        loop {
            let pivot_col = self.find_pivot_col();
            if pivot_col.is_none() {
                break;
            }
            let pivot_col = pivot_col.unwrap();
            let pivot_row = self.find_pivot_row(pivot_col);
            self.pivot(pivot_row, pivot_col);
        }
        self.extract_solution()
    }
}

impl Simplex {
    fn find_pivot_col(&self) -> Option<usize> {
        self.tableau.slice(s![-1, ..-1])
            .iter()
            .enumerate()
            .filter(|&(_, &value)| value < 0.0)
            .min_by(|a, b| a.1.partial_cmp(b.1).unwrap())
            .map(|(index, _)| index)
    }

    fn find_pivot_row(&self, pivot_col: usize) -> usize {
        self.tableau.slice(s![..-1, pivot_col])
            .iter()
            .enumerate()
            .filter_map(|(index, &value)| {
                if value > 0.0 {
                    Some((index, self.tableau[[index, self.tableau.ncols() - 1]] / value))
                } else {
                    None
                }
            })
            .min_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
            .unwrap().0
    }

    fn pivot(&mut self, pivot_row: usize, pivot_col: usize) {
        let pivot_value = self.tableau[[pivot_row, pivot_col]];
        self.tableau.row_mut(pivot_row).mapv_inplace(|x| x / pivot_value);
        for row in 0..self.tableau.nrows() {
            if row != pivot_row {
                let multiplier = self.tableau[[row, pivot_col]];
                let pivot_row_scaled = self.tableau.row(pivot_row).mapv(|x| x * multiplier);
                self.tableau.row_mut(row).zip_mut_with(&pivot_row_scaled, |a, &b| *a -= b);
            }
        }
    }

    fn extract_solution(&self) -> Vec<f64> {
        let mut solution = vec![0.0; self.tableau.ncols() - 1];
        // Iterate over rows (axis 0) of the tableau slice
        for (index, row) in self.tableau.slice(s![..-1, ..-1]).outer_iter().enumerate() {
            if let Some((var_index, _)) = row.iter().enumerate().find(|(_, &value)| value == 1.0) {
                solution[var_index] = self.tableau[[index, self.tableau.ncols() - 1]];
            }
        }
        solution
    }

}

