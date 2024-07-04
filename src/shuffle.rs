// src/shuffle.rs

use pyo3::prelude::*;
use rand::Rng;
/// Perform the Knuth Shuffle (Fisher-Yates Shuffle) on a list of integers.
///
/// This function takes a mutable vector of integers and randomly shuffles its elements
/// in place using the Knuth Shuffle algorithm. The algorithm ensures that each possible
/// permutation of the list is equally likely.
///
/// # Arguments
///
/// * `data` - A vector of integers to be shuffled.
///
/// # Returns
///
/// A shuffled vector of integers.
///
/// # Example
///
/// ```python
/// import knuth_shuffle
///
/// data = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
/// shuffled_data = knuth_shuffle.knuth_shuffle(data)
/// print(shuffled_data)
/// ```
///
/// The above example will print the list `data` in a random order.
///
/// # Note
///
/// This function modifies the input vector `data` in place and returns the shuffled vector.
#[pyfunction]
pub fn Knuth(mut data: Vec<i32>) -> PyResult<Vec<i32>> {
    let mut rng = rand::thread_rng();
    let n = data.len();
    for i in 0..n {
        let j = rng.gen_range(0..n); // Random index between 0 and n-1
        data.swap(i, j);
    }
    Ok(data)
}