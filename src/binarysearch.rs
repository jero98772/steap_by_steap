use pyo3::prelude::*;
/// Perform a binary search on a sorted array of integers.
///
/// # Arguments
///
/// * `array`: A sorted vector of integers.
/// * `target`: The integer value to search for in the array.
///
/// # Returns
///
/// `Option<usize>`: Returns `Some(index)` if `target` is found in `array`, where `index` is the index of the `target` in the array.
/// Returns `None` if `target` is not found in the array.
#[pyfunction]
pub fn Binary_search(array: Vec<i32>, target: i32) -> Option<usize> {
    let mut low = 0;
    let mut high = array.len() - 1;

    while low <= high {
        let mid = low + (high - low) / 2;
        if array[mid] == target {
            return Some(mid);
        } else if array[mid] < target {
            low = mid + 1;
        } else {
            high = mid - 1;
        }
    }

    None
}

