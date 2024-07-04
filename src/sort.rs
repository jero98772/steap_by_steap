// src/sort.rs
use pyo3::prelude::*;
use pyo3::types::PyList;

/// Merges two subarrays of `arr`.
///
/// # Arguments
///
/// * `arr` - The array to be sorted.
/// * `left` - The starting index of the left subarray.
/// * `mid` - The ending index of the left subarray and starting index of the right subarray.
/// * `right` - The ending index of the right subarray.
fn merge(arr: &mut [i32], left: usize, mid: usize, right: usize) {
    let mut left_part = arr[left..mid+1].to_vec();
    let mut right_part = arr[mid+1..right+1].to_vec();

    left_part.push(i32::MAX);
    right_part.push(i32::MAX);

    let mut i = 0;
    let mut j = 0;

    for k in left..=right {
        if left_part[i] <= right_part[j] {
            arr[k] = left_part[i];
            i += 1;
        } else {
            arr[k] = right_part[j];
            j += 1;
        }
    }
}
/// Recursively divides the array into subarrays and merges them in sorted order.
///
/// # Arguments
///
/// * `arr` - The array to be sorted.
/// * `left` - The starting index of the subarray to be sorted.
/// * `right` - The ending index of the subarray to be sorted.
fn merge_sort_helper(arr: &mut [i32], left: usize, right: usize) {
    if left < right {
        let mid = left + (right - left) / 2;
        merge_sort_helper(arr, left, mid);
        merge_sort_helper(arr, mid + 1, right);
        merge(arr, left, mid, right);
    }
}
/// Partitions the array into two parts and returns the index of the pivot element.
///
/// # Arguments
///
/// * `arr` - The array to be partitioned.
/// * `low` - The starting index of the subarray to be partitioned.
/// * `high` - The ending index of the subarray to be partitioned.
///
/// # Returns
///
/// The index of the pivot element.
fn partition(arr: &mut [i32], low: usize, high: usize) -> usize {
    let pivot = arr[high];
    let mut i = low;
    for j in low..high {
        if arr[j] < pivot {
            arr.swap(i, j);
            i += 1;
        }
    }
    arr.swap(i, high);
    i
}
/// Recursively sorts the array using the Quick Sort algorithm.
///
/// # Arguments
///
/// * `arr` - The array to be sorted.
/// * `low` - The starting index of the subarray to be sorted.
/// * `high` - The ending index of the subarray to be sorted.
fn quick_sort_helper(arr: &mut [i32], low: usize, high: usize) {
    if low < high {
        let pi = partition(arr, low, high);
        if pi > 0 { quick_sort_helper(arr, low, pi - 1); }
        quick_sort_helper(arr, pi + 1, high);
    }
}

/// Sorts the array using the Selection Sort algorithm.
///
/// # Arguments
///
/// * `arr` - The array to be sorted.
///
/// # Returns
///
/// The sorted array.
#[pyfunction]
pub fn Selection(mut arr: Vec<i32>) -> PyResult<Vec<i32>> {
    let len = arr.len();
    for i in 0..len {
        let mut min_idx = i;
        for j in (i + 1)..len {
            if arr[j] < arr[min_idx] {
                min_idx = j;
            }
        }
        arr.swap(i, min_idx);
    }
    Ok(arr)
}
/// Sorts the array using the Insertion Sort algorithm.
///
/// # Arguments
///
/// * `arr` - The array to be sorted.
///
/// # Returns
///
/// The sorted array.
#[pyfunction]
pub fn Insertion(mut arr: Vec<i32>) -> PyResult<Vec<i32>> {
    let len = arr.len();
    for i in 1..len {
        let key = arr[i];
        let mut j = i as isize - 1;
        while j >= 0 && arr[j as usize] > key {
            arr[(j + 1) as usize] = arr[j as usize];
            j -= 1;
        }
        arr[(j + 1) as usize] = key;
    }
    Ok(arr)
}

/// Sorts the array using the Shell Sort algorithm.
///
/// # Arguments
///
/// * `arr` - The array to be sorted.
///
/// # Returns
///
/// The sorted array.
#[pyfunction]
pub fn Shell(mut arr: Vec<i32>) -> PyResult<Vec<i32>> {
    let n = arr.len();
    let mut gap = n / 2;
    while gap > 0 {
        for i in gap..n {
            let temp = arr[i];
            let mut j = i;
            while j >= gap && arr[j - gap] > temp {
                arr[j] = arr[j - gap];
                j -= gap;
            }
            arr[j] = temp;
        }
        gap /= 2;
    }
    Ok(arr)
}


/// Sorts the array using the Quick Sort algorithm.
///
/// # Arguments
///
/// * `arr` - The array to be sorted.
///
/// # Returns
///
/// The sorted array.
#[pyfunction]
pub fn Quick(mut arr: Vec<i32>) -> PyResult<Vec<i32>> {
    let len = arr.len();
    if len > 1 {
        quick_sort_helper(&mut arr, 0, len - 1);
    }
    Ok(arr)
}

/// Sorts the array using the Merge Sort algorithm.
///
/// # Arguments
///
/// * `arr` - The array to be sorted.
///
/// # Returns
///
/// The sorted array.
#[pyfunction]
pub fn Merge(mut arr: Vec<i32>) -> PyResult<Vec<i32>> {
    let len = arr.len();
    if len > 1 {
        merge_sort_helper(&mut arr, 0, len - 1);
    }
    Ok(arr)
}


/// Sorts a list of integers using LSD (Least Significant Digit) Radix Sort.
///
/// # Arguments
///
/// * `arr` - The vector of integers to be sorted.
///
/// # Returns
///
/// A sorted vector of integers.
///

#[pyfunction]
pub fn LsdRadix(mut arr: Vec<u32>) -> PyResult<Vec<u32>> {
    if arr.is_empty() {
        return Ok(arr);
    }

    let max_value = *arr.iter().max().unwrap_or(&0);

    let mut exp = 1;
    let mut output = vec![0; arr.len()];

    while exp <= max_value {
        let mut count = vec![0; 10];

        for &num in &arr {
            count[((num / exp) % 10) as usize] += 1;
        }

        for i in 1..10 {
            count[i] += count[i - 1];
        }

        for i in (0..arr.len()).rev() {
            let digit = ((arr[i] / exp) % 10) as usize;
            output[count[digit] - 1] = arr[i];
            count[digit] -= 1;
        }

        for i in 0..arr.len() {
            arr[i] = output[i];
        }

        exp *= 10;
    }

    Ok(arr)
}

/// Perform MSD Radix Sort on a list of strings.
///
/// This function implements the Most Significant Digit (MSD) Radix Sort algorithm
/// to sort a list of strings in lexicographic order.
///
/// Args:
///     strings (List[str]): A list of strings to be sorted.
///
/// Returns:
///     List[str]: A new list containing the input strings in sorted order.
///
/// Example:
///     >>> msd_radix_sort(["cat", "dog", "bird", "ant"])
///     ["ant", "bird", "cat", "dog"]
#[pyfunction]
pub fn MsdRadix(strings: &PyList) -> PyResult<Vec<String>> {
    let mut vec: Vec<String> = strings.extract()?;
    if vec.is_empty() {
        return Ok(vec);
    }

    let len = vec.len();
    let max_len = vec.iter().map(|s| s.len()).max().unwrap();
    msd_radix_sort_helper(&mut vec, 0, len, 0, max_len);
   
    Ok(vec)
}

/// Helper function for MSD Radix Sort.
///
/// This recursive function performs the actual sorting of a subset of the strings.
///
/// Args:
///     vec: Mutable reference to the vector of strings being sorted.
///     lo: Starting index of the current subset.
///     hi: Ending index (exclusive) of the current subset.
///     d: Current digit (character position) being examined.
///     max_len: Maximum length of any string in the original input.
fn msd_radix_sort_helper(vec: &mut [String], lo: usize, hi: usize, d: usize, max_len: usize) {
    if hi <= lo + 1 || d >= max_len {
        return;
    }

    let r = 256; // Assuming ASCII characters
    let mut count = vec![0; r + 2];

    // Compute frequency counts
    for i in lo..hi {
        count[char_at(&vec[i], d) + 2] += 1;
    }

    // Transform counts to indices
    for i in 0..r + 1 {
        count[i + 1] += count[i];
    }

    // Distribute
    let mut aux = vec![String::new(); hi - lo];
    for i in lo..hi {
        let c = char_at(&vec[i], d);
        aux[count[c + 1]] = vec[i].clone();
        count[c + 1] += 1;
    }

    // Copy back
    for i in lo..hi {
        vec[i] = aux[i - lo].clone();
    }

    // Recursively sort for each character
    for i in 0..r {
        msd_radix_sort_helper(vec, lo + count[i], lo + count[i + 1], d + 1, max_len);
    }
}

/// Get the character at a specific index in a string.
///
/// If the index is out of bounds, return -1.
///
/// Args:
///     s: Reference to the string.
///     d: Index of the character to retrieve.
///
/// Returns:
///     usize: ASCII value of the character, or -1 if out of bounds.
fn char_at(s: &str, d: usize) -> usize {
    if d < s.len() {
        s.as_bytes()[d] as usize
    } else {
        0
    }
}

/// Sorts a list of strings using 3-way Radix Quicksort.
///
/// # Arguments
///
/// * `arr_py` - Python list of strings to be sorted.
///
/// # Returns
///
/// A sorted vector of strings.
///
/// # Examples
///
/// ```
/// # use radix_quicksort::radix_quicksort;
/// # use pyo3::types::PyList;
/// # use pyo3::Python;
/// let gil = Python::acquire_gil();
/// let py = gil.python();
/// let arr_py = PyList::new(py, &["bc", "ab", "aa", "cb", "ac", "ca", "bb", "ba"]).unwrap();
/// let sorted_arr = radix_quicksort(arr_py).unwrap();
/// assert_eq!(sorted_arr, vec!["aa", "ab", "ac", "ba", "bb", "bc", "ca", "cb"]);
/// ```
#[pyfunction]
pub fn RadixQuicksort(arr_py: &PyList) -> PyResult<Vec<&str>> {
    let mut arr: Vec<&str> = Vec::new();

    for item in arr_py.iter() {
        let s = item.extract::<&str>()?;
        arr.push(s);
    }

    if arr.is_empty() {
        return Ok(arr);
    }

    let mut output = vec![String::new(); arr.len()];
    let len = arr.len();
    radix_quicksort_helper(&mut arr, &mut output, 0, len - 1, 0);

    Ok(arr)
}

fn radix_quicksort_helper(arr: &mut [&str], output: &mut [String], left: usize, right: usize, d: usize) {
    if left >= right || d >= arr[0].len() {
        return;
    }

    let mut lo = left;
    let mut hi = right;
    let pivot = get_char(arr[left], d);

    let mut i = left + 1;
    while i <= hi {
        let curr = get_char(arr[i], d);
        if curr < pivot {
            arr.swap(lo, i);
            lo += 1;
            i += 1;
        } else if curr > pivot {
            arr.swap(i, hi);
            if hi > 0 {
                hi -= 1;
            }
        } else {
            i += 1;
        }
    }

    radix_quicksort_helper(arr, output, left, lo - 1, d);
    if pivot != '\0' {
        radix_quicksort_helper(arr, output, lo, hi, d + 1);
    }
    radix_quicksort_helper(arr, output, hi + 1, right, d);
}

fn get_char(s: &str, d: usize) -> char {
    if d < s.len() {
        s.chars().nth(d).unwrap_or('\0')
    } else {
        '\0'
    }
}
