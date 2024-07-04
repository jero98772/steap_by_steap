use pyo3::prelude::*;

/// Perform brute force substring search.
///
/// # Arguments
///
/// * `text` - The text to search within.
/// * `pattern` - The pattern to search for.
///
/// # Returns
///
/// Returns the index of the first occurrence of `pattern` in `text`, or `-1` if not found.
#[pyfunction]
pub fn BrutalForceSearch(text: &str, pattern: &str) -> isize {
    let n = text.len();
    let m = pattern.len();

    for i in 0..=(n - m) {
        let mut j = 0;
        while j < m && pattern.as_bytes()[j] == text.as_bytes()[i + j] {
            j += 1;
        }
        if j == m {
            return i as isize;
        }
    }

    -1
}


/// Returns a vector of indices where the pattern matches in the text using KMP algorithm.
///
/// # Arguments
///
/// * `text` - The text to search for the pattern.
/// * `pattern` - The pattern to search for in the text.
///
/// # Returns
///
/// A Python list containing the indices where the pattern matches in the text.
#[pyfunction]
pub fn KMPSearch(text: &str, pattern: &str) -> PyResult<Vec<usize>> {
    // Build the KMP table (prefix function)
    let mut kmp_table = vec![0; pattern.len()];
    let mut j = 0;

    for (i, c) in pattern.chars().enumerate().skip(1) {
        while j > 0 && c != pattern.chars().nth(j).unwrap() {
            j = kmp_table[j - 1];
        }
        if c == pattern.chars().nth(j).unwrap() {
            j += 1;
            kmp_table[i] = j;
        }
    }

    // Perform the search
    let mut matches = vec![];
    let mut i = 0;
    let mut j = 0;

    while i < text.len() {
        if pattern.chars().nth(j).unwrap() == text.chars().nth(i).unwrap() {
            i += 1;
            j += 1;
        }

        if j == pattern.len() {
            matches.push(i - j);
            j = kmp_table[j - 1];
        } else if i < text.len() && pattern.chars().nth(j).unwrap() != text.chars().nth(i).unwrap() {
            if j != 0 {
                j = kmp_table[j - 1];
            } else {
                i += 1;
            }
        }
    }

    Ok(matches)
}


/// Implements the Boyer-Moore string search algorithm.
#[pyfunction]
pub fn BoyerMooreSearch(text: &str, pattern: &str) -> Option<usize> {
    let n = text.len();
    let m = pattern.len();

    if m == 0 {
        return Some(0); // Empty pattern matches at the start
    }

    let mut bad_char_skip = vec![m; 256]; // Assuming ASCII characters

    for (i, &ch) in pattern[..m-1].as_bytes().iter().enumerate() {
        bad_char_skip[ch as usize] = (m - 1 - i) as usize;
    }

    let mut i = m - 1;
    while i < n {
        let mut j = m - 1;
        while text.as_bytes()[i] == pattern.as_bytes()[j] {
            if j == 0 {
                return Some(i);
            }
            i -= 1;
            j -= 1;
        }
        i += bad_char_skip[text.as_bytes()[i] as usize].max(1) as usize;
    }

    None
}

use pyo3::prelude::*;
use pyo3::wrap_pyfunction;

/// Rabin-Karp algorithm for substring search.
///
/// # Arguments
///
/// * `text` - The text in which to search for the pattern.
/// * `pattern` - The pattern to search for.
/// * `prime` - A prime number to use for hashing.
///
/// # Returns
///
/// A list of starting indices where the pattern is found in the text.
#[pyfunction]
pub fn RabinKarpSearch(text: &str, pattern: &str, prime: u64) -> Vec<usize> {
    let n = text.len();
    let m = pattern.len();
    let mut result = Vec::new();
    let base: u64 = 256;
    
    if m > n {
        return result;
    }
    
    // Compute the hash value of the pattern and the first window of the text
    let mut pattern_hash: u64 = 0;
    let mut text_hash: u64 = 0;
    let mut h: u64 = 1;

    for _ in 0..m-1 {
        h = (h * base) % prime;
    }

    for i in 0..m {
        pattern_hash = (base * pattern_hash + pattern.as_bytes()[i] as u64) % prime;
        text_hash = (base * text_hash + text.as_bytes()[i] as u64) % prime;
    }

    // Slide the pattern over the text one by one
    for i in 0..=n-m {
        // Check the hash values of current window of text and pattern
        if pattern_hash == text_hash {
            // Check for characters one by one
            let mut j = 0;
            while j < m {
                if text.as_bytes()[i+j] != pattern.as_bytes()[j] {
                    break;
                }
                j += 1;
            }
            if j == m {
                result.push(i);
            }
        }
        // Calculate hash value for next window of text
        if i < n-m {
            text_hash = (base * (text_hash - (text.as_bytes()[i] as u64 * h) % prime) + text.as_bytes()[i+m] as u64) % prime;
            if text_hash < 0 {
                text_hash = (text_hash + prime) % prime;
            }
        }
    }

    result
}

