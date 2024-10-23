use pyo3::prelude::*;
use pyo3::types::PyList;
use std::cmp::Ordering;

#[pyclass]
/// A struct representing a Suffix Array.
pub struct SuffixArray {
    text: String,
    sa: Vec<usize>,
}

#[pymethods]
impl SuffixArray {
    #[new]
    /// Create a new SuffixArray from the given text.
    ///
    /// Args:
    ///     text (str): The input text to build the suffix array from.
    ///
    /// Returns:
    ///     SuffixArray: A new SuffixArray instance.
    fn new(text: &str) -> Self {
        let mut sa = SuffixArray {
            text: text.to_string(),
            sa: (0..text.len()).collect(),
        };
        sa.build_suffix_array();
        sa
    }

    /// Get the suffix array.
    ///
    /// Returns:
    ///     List[int]: The suffix array as a list of integer indices.
    fn get_suffix_array(&self) -> PyResult<Vec<usize>> {
        Ok(self.sa.clone())
    }

    /// Perform a binary search to find occurrences of a pattern in the text.
    ///
    /// Args:
    ///     pattern (str): The pattern to search for.
    ///
    /// Returns:
    ///     List[int]: A list of starting positions where the pattern occurs in the text.
    fn search(&self, pattern: &str) -> PyResult<Vec<usize>> {
        let mut left = 0;
        let mut right = self.sa.len();
        
        // Handle empty pattern or text
        if pattern.is_empty() || self.text.is_empty() {
            return Ok(Vec::new());
        }

        while left < right {
            let mid = (left + right) / 2;
            let suffix = &self.text[self.sa[mid]..];
            
            if suffix.len() < pattern.len() {
                match pattern.cmp(&suffix) {
                    Ordering::Less => right = mid,
                    Ordering::Greater => left = mid + 1,
                    Ordering::Equal => break,
                }
            } else {
                match pattern.cmp(&suffix[..pattern.len()]) {
                    Ordering::Less => right = mid,
                    Ordering::Greater => left = mid + 1,
                    Ordering::Equal => break,
                }
            }
        }

        let mut results = Vec::new();
        while left < self.sa.len() {
            let suffix = &self.text[self.sa[left]..];
            if !suffix.starts_with(pattern) {
                break;
            }
            results.push(self.sa[left]);
            left += 1;
        }
        Ok(results)
    }
}

impl SuffixArray {
    fn build_suffix_array(&mut self) {
        let n = self.text.len();
        if n == 0 {
            return;
        }

        let mut rank = vec![0; n];
        let mut tmp = vec![0; n];

        // Initialize ranks with ASCII values
        for (i, &c) in self.text.as_bytes().iter().enumerate() {
            rank[i] = c as usize;
        }

        let mut k = 1;
        while k < n {
            // Sort suffixes based on their first 2*k characters
            self.sa.sort_by_key(|&i| {
                let next_rank = if i + k < n { rank[i + k] } else { 0 };
                (rank[i], next_rank)
            });

            // Update ranks
            tmp[self.sa[0]] = 0;
            for i in 1..n {
                let curr_pair = (
                    rank[self.sa[i]], 
                    if self.sa[i] + k < n { rank[self.sa[i] + k] } else { 0 }
                );
                let prev_pair = (
                    rank[self.sa[i - 1]], 
                    if self.sa[i - 1] + k < n { rank[self.sa[i - 1] + k] } else { 0 }
                );
                
                tmp[self.sa[i]] = tmp[self.sa[i - 1]] + (curr_pair != prev_pair) as usize;
            }

            // Swap rank arrays
            std::mem::swap(&mut rank, &mut tmp);

            // Early termination if all suffixes are sorted
            if rank[self.sa[n - 1]] == n - 1 {
                break;
            }

            k *= 2;
        }
    }
}