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

        while left < right {
            let mid = (left + right) / 2;
            let suffix = &self.text[self.sa[mid]..];
            match suffix.starts_with(pattern) {
                true => right = mid,
                false => match pattern.cmp(&suffix[..pattern.len().min(suffix.len())]) {
                    Ordering::Less => right = mid,
                    Ordering::Greater => left = mid + 1,
                    Ordering::Equal => break,
                },
            }
        }

        let mut results = Vec::new();
        while left < self.sa.len() && self.text[self.sa[left]..].starts_with(pattern) {
            results.push(self.sa[left]);
            left += 1;
        }

        Ok(results)
    }
}

impl SuffixArray {
    fn build_suffix_array(&mut self) {
        let n = self.text.len();
        let mut rank = vec![0; n];
        let mut tmp = vec![0; n];

        // Initialize ranks
        for (i, &c) in self.text.as_bytes().iter().enumerate() {
            rank[i] = c as usize;
        }

        for k in 1..n {
            self.sa.sort_by_key(|&i| {
                if i + k < n {
                    (rank[i], rank[i + k])
                } else {
                    (rank[i], 0)
                }
            });

            tmp[self.sa[0]] = 0;
            for i in 1..n {
                tmp[self.sa[i]] = tmp[self.sa[i - 1]]
                    + if (rank[self.sa[i]], rank[self.sa[i] + k.min(n - self.sa[i])]) 
                         != (rank[self.sa[i - 1]], rank[self.sa[i - 1] + k.min(n - self.sa[i - 1])]) {
                        1
                    } else {
                        0
                    };
            }
            std::mem::swap(&mut rank, &mut tmp);

            if rank[self.sa[n - 1]] == n - 1 {
                break;
            }
        }
    }
}
