use pyo3::prelude::*;
use std::collections::{BinaryHeap, HashMap};
use std::cmp::Ordering;

// Define a structure for the Huffman Tree node
#[derive(Debug, Eq, PartialEq)]
struct HuffmanNode {
    freq: usize,
    ch: Option<char>,
    left: Option<Box<HuffmanNode>>,
    right: Option<Box<HuffmanNode>>,
}

// Implementing the Ord and PartialOrd traits to use HuffmanNode in a BinaryHeap
impl Ord for HuffmanNode {
    fn cmp(&self, other: &Self) -> Ordering {
        other.freq.cmp(&self.freq)
    }
}

impl PartialOrd for HuffmanNode {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl HuffmanNode {
    // Create a new leaf node
    fn new_leaf(ch: char, freq: usize) -> Self {
        HuffmanNode {
            freq,
            ch: Some(ch),
            left: None,
            right: None,
        }
    }

    // Create a new internal node
    fn new_internal(freq: usize, left: HuffmanNode, right: HuffmanNode) -> Self {
        HuffmanNode {
            freq,
            ch: None,
            left: Some(Box::new(left)),
            right: Some(Box::new(right)),
        }
    }

    // Generate Huffman codes from the tree
    fn generate_codes(&self, prefix: String, codes: &mut HashMap<char, String>) {
        if let Some(ch) = self.ch {
            codes.insert(ch, prefix);
        } else {
            if let Some(ref left) = self.left {
                left.generate_codes(format!("{}0", prefix), codes);
            }
            if let Some(ref right) = self.right {
                right.generate_codes(format!("{}1", prefix), codes);
            }
        }
    }
}

/// Generate Huffman codes for the input string
///
/// # Arguments
///
/// * `input` - A string slice that holds the input text
///
/// # Returns
///
/// * A dictionary with characters as keys and their corresponding Huffman codes as values
#[pyfunction]
pub fn HuffmanCodes(input: &str) -> PyResult<HashMap<char, String>> {
    let mut freq_map = HashMap::new();

    // Calculate the frequency of each character
    for ch in input.chars() {
        *freq_map.entry(ch).or_insert(0) += 1;
    }

    // Build a min-heap using a binary heap
    let mut heap = BinaryHeap::new();
    for (ch, freq) in freq_map.iter() {
        heap.push(HuffmanNode::new_leaf(*ch, *freq));
    }

    // Construct the Huffman Tree
    while heap.len() > 1 {
        let left = heap.pop().unwrap();
        let right = heap.pop().unwrap();
        let freq_sum = left.freq + right.freq;
        heap.push(HuffmanNode::new_internal(freq_sum, left, right));
    }

    let root = heap.pop().unwrap();
    let mut codes = HashMap::new();
    root.generate_codes(String::new(), &mut codes);

    Ok(codes)
}




/// Run-length encodes a string.
///
/// # Arguments
///
/// * `s` - A string slice to be compressed.
///
/// # Returns
///
/// * A `String` containing the run-length encoded representation of the input string.
///
/// # Example
///
/// ```python
/// from your_module import run_length_encode
/// compressed = run_length_encode("aaabbbccc")
/// print(compressed)  # Output: "a3b3c3"
/// ```
#[pyfunction]
pub fn RunLengthEncode(s: &str) -> String {
    if s.is_empty() {
        return String::new();
    }

    let mut encoded = String::new();
    let mut chars = s.chars();
    let mut current_char = chars.next().unwrap();
    let mut count = 1;

    for c in chars {
        if c == current_char {
            count += 1;
        } else {
            encoded.push(current_char);
            encoded.push_str(&count.to_string());
            current_char = c;
            count = 1;
        }
    }
    
    encoded.push(current_char);
    encoded.push_str(&count.to_string());

    encoded
}

/// Run-length decodes a string.
///
/// # Arguments
///
/// * `s` - A run-length encoded string slice to be decompressed.
///
/// # Returns
///
/// * A `String` containing the original uncompressed representation of the input string.
///
/// # Example
///
/// ```python
/// from your_module import run_length_decode
/// decompressed = run_length_decode("a3b3c3")
/// print(decompressed)  # Output: "aaabbbccc"
/// ```
#[pyfunction]
pub fn RunLengthDecode(s: &str) -> String {
    let mut decoded = String::new();
    let mut chars = s.chars();

    while let Some(c) = chars.next() {
        if let Some(digit) = chars.next() {
            if let Some(count) = digit.to_digit(10) {
                for _ in 0..count {
                    decoded.push(c);
                }
            }
        }
    }

    decoded
}



/// Compresses the input string using the LZW compression algorithm.
///
/// # Arguments
///
/// * `input` - A string slice that holds the input string to be compressed.
///
/// # Returns
///
/// A vector of integers representing the compressed data.
#[pyfunction]
pub fn LZWCompress(input: &str) -> Vec<u16> {
    let mut dict: HashMap<String, u16> = HashMap::new();
    let mut dict_size = 256;
    for i in 0..256 {
        dict.insert((i as u8 as char).to_string(), i);
    }

    let mut w = String::new();
    let mut result = Vec::new();

    for c in input.chars() {
        let wc = format!("{}{}", w, c);
        if dict.contains_key(&wc) {
            w = wc;
        } else {
            result.push(*dict.get(&w).unwrap());
            dict.insert(wc, dict_size);
            dict_size += 1;
            w = c.to_string();
        }
    }

    if !w.is_empty() {
        result.push(*dict.get(&w).unwrap());
    }

    result
}

/// Decompresses the compressed data using the LZW decompression algorithm.
///
/// # Arguments
///
/// * `compressed` - A vector of integers representing the compressed data.
///
/// # Returns
///
/// A string representing the decompressed data.
#[pyfunction]
pub fn LZWDecompress(compressed: Vec<u16>) -> String {
    let mut dict: HashMap<u16, String> = HashMap::new();
    let mut dict_size = 256;
    for i in 0..256 {
        dict.insert(i, (i as u8 as char).to_string());
    }

    let mut w = (compressed[0] as u8 as char).to_string();
    let mut result = w.clone();
    for &k in &compressed[1..] {
        let entry = if dict.contains_key(&k) {
            dict.get(&k).unwrap().clone()
        } else if k == dict_size {
            format!("{}{}", w, w.chars().next().unwrap())
        } else {
            panic!("Invalid compressed k");
        };

        result.push_str(&entry);

        let wc = format!("{}{}", w, entry.chars().next().unwrap());
        dict.insert(dict_size, wc);
        dict_size += 1;

        w = entry;
    }

    result
}
