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
    let mut results = Vec::new();

    // Handle empty pattern or text
    if pattern.is_empty() || self.text.is_empty() {
        return Ok(results);
    }

    // Perform binary search to find the first occurrence of the pattern
    while left < right {
        let mid = (left + right) / 2;
        let suffix = &self.text[self.sa[mid]..];

        let cmp_result = if suffix.len() < pattern.len() {
            pattern.cmp(suffix)
        } else {
            pattern.cmp(&suffix[..pattern.len()])
        };

        match cmp_result {
            Ordering::Less => right = mid,
            Ordering::Greater => left = mid + 1,
            Ordering::Equal => {
                // If we found a match, find all occurrences
                let mut match_pos = mid;

                // Check to the left for any more matches
                while match_pos > 0 && self.text[self.sa[match_pos - 1]..].starts_with(pattern) {
                    match_pos -= 1;
                }

                // Collect all matching positions
                while match_pos < self.sa.len() && self.text[self.sa[match_pos]..].starts_with(pattern) {
                    results.push(self.sa[match_pos]);
                    match_pos += 1;
                }

                return Ok(results);
            }
        }
    }

    Ok(results)
}

    /// Get all suffixes of the text.
    ///
    /// Returns:
    ///     List[str]: A list of all suffixes in the text.
    fn get_suffixes(&self) -> PyResult<Vec<String>> {
        let suffixes: Vec<String> = self.sa.iter().map(|&i| self.text[i..].to_string()).collect();
        Ok(suffixes)
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
