use pyo3::prelude::*;
use std::collections::{BinaryHeap, HashMap};
use std::cmp::Ordering;

use image::{open, ImageBuffer, Rgb, DynamicImage, RgbImage};
use std::fs::File;
use std::path::Path;
use rustfft::{FftPlanner, num_complex::Complex};
use pyo3::exceptions::PyIOError;


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
    // Decode a binary string back to the original text using the Huffman Tree
    fn decode(&self, encoded: &str) -> String {
        let mut result = String::new();
        let mut current_node = self;
        for bit in encoded.chars() {
            current_node = if bit == '0' {
                current_node.left.as_deref().unwrap()
            } else {
                current_node.right.as_deref().unwrap()
            };

            if let Some(ch) = current_node.ch {
                result.push(ch);
                current_node = self;  // Reset to root for next character
            }
        }
        result
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

/// Huffman Encoding/Compression
///
/// # Arguments
/// * `input` - A string slice that holds the input text
///
/// # Returns
/// * A tuple with compressed binary string and the corresponding Huffman tree
#[pyfunction]
pub fn HuffmanCompress(input: &str) -> PyResult<(String, HashMap<char, String>)> {
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

    // Compress the input string
    let compressed: String = input.chars().map(|ch| codes[&ch].clone()).collect();

    Ok((compressed, codes))
}

/// Huffman Decompression
///
/// # Arguments
/// * `compressed` - The compressed binary string
/// * `codes` - The Huffman Tree used for compression
///
/// # Returns
/// * The original uncompressed string
#[pyfunction]
pub fn HuffmanDecompress(compressed: &str, codes: HashMap<char, String>) -> PyResult<String> {
    // Reverse the Huffman codes to map from code to char
    let mut reverse_codes = HashMap::new();
    for (ch, code) in codes {
        reverse_codes.insert(code, ch);
    }

    // Decompress the binary string back to the original text
    let mut decoded = String::new();
    let mut buffer = String::new();
    for bit in compressed.chars() {
        buffer.push(bit);
        if let Some(ch) = reverse_codes.get(&buffer) {
            decoded.push(*ch);
            buffer.clear();
        }
    }

    Ok(decoded)
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


/// Compress a color image using FFT.
///
/// This function reads the input color image, applies FFT to each color channel,
/// zeroes out small frequency components based on the provided compression ratio,
/// and saves the compressed image to the specified output path.
///
/// # Arguments
///
/// * `input_path` - A string slice that holds the file path of the input image.
/// * `output_path` - A string slice that holds the file path to save the compressed image.
/// * `compression_ratio` - A floating point value between 0 and 1 that determines the percentage of frequencies to retain.
///
/// # Example
/// ```python
/// fft_image_compression.compress_image("input.png", "compressed.png", 0.1)
/// ```
/// This will compress the image, retaining only 10% of the frequencies.
#[pyfunction]
pub fn CompressImageFFT(input_path: &str, output_path: &str, compression_ratio: f32) -> PyResult<()> {
    // Validate compression ratio
    if !(0.0..=1.0).contains(&compression_ratio) {
        return Err(PyErr::new::<pyo3::exceptions::PyValueError, _>(
            "Compression ratio must be between 0 and 1"
        ));
    }

    // Open image
    let img = match open(input_path) {
        Ok(img) => img.to_rgb8(),
        Err(err) => return Err(PyIOError::new_err(err.to_string())),
    };

    let (width, height) = img.dimensions();
    let size = (width * height) as usize;

    // Process each channel separately
    let mut red_channel: Vec<Complex<f32>> = Vec::with_capacity(size);
    let mut green_channel: Vec<Complex<f32>> = Vec::with_capacity(size);
    let mut blue_channel: Vec<Complex<f32>> = Vec::with_capacity(size);

    // Split into channels
    for pixel in img.pixels() {
        red_channel.push(Complex::new(pixel[0] as f32, 0.0));
        green_channel.push(Complex::new(pixel[1] as f32, 0.0));
        blue_channel.push(Complex::new(pixel[2] as f32, 0.0));
    }

    // Process each channel
    let processed_red = process_channel(&mut red_channel, width, height, compression_ratio)?;
    let processed_green = process_channel(&mut green_channel, width, height, compression_ratio)?;
    let processed_blue = process_channel(&mut blue_channel, width, height, compression_ratio)?;

    // Combine channels back into an RGB image
    let mut output_img: RgbImage = ImageBuffer::new(width, height);
    for y in 0..height {
        for x in 0..width {
            let idx = (y * width + x) as usize;
            let red = processed_red[idx].max(0.0).min(255.0) as u8;
            let green = processed_green[idx].max(0.0).min(255.0) as u8;
            let blue = processed_blue[idx].max(0.0).min(255.0) as u8;
            output_img.put_pixel(x, y, Rgb([red, green, blue]));
        }
    }

    // Save the result
    if let Err(err) = output_img.save(output_path) {
        return Err(PyIOError::new_err(err.to_string()));
    }

    Ok(())
}

/// Helper function to process a single color channel
fn process_channel(
    buffer: &mut Vec<Complex<f32>>,
    width: u32,
    height: u32,
    compression_ratio: f32,
) -> PyResult<Vec<f32>> {
    let size = (width * height) as usize;
    let mut planner = FftPlanner::new();

    // Forward FFT on rows
    let row_fft = planner.plan_fft_forward(width as usize);
    for row in buffer.chunks_mut(width as usize) {
        row_fft.process(row);
    }

    // Forward FFT on columns
    let mut temp = vec![Complex::new(0.0, 0.0); size];
    for x in 0..width as usize {
        let mut column: Vec<Complex<f32>> = (0..height as usize)
            .map(|y| buffer[y * width as usize + x])
            .collect();
        
        let col_fft = planner.plan_fft_forward(height as usize);
        col_fft.process(&mut column);
        
        for (y, &value) in column.iter().enumerate() {
            temp[y * width as usize + x] = value;
        }
    }
    *buffer = temp;

    // Calculate magnitudes and find threshold
    let mut magnitudes: Vec<(usize, f32)> = buffer.iter()
        .enumerate()
        .map(|(i, &c)| (i, (c.re * c.re + c.im * c.im).sqrt()))
        .collect();
    
    magnitudes.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(Ordering::Equal));
    
    let keep = (size as f32 * (1.0 - compression_ratio)) as usize;
    let threshold = magnitudes.get(keep)
        .map(|&(_, mag)| mag)
        .unwrap_or(0.0);

    // Apply threshold
    for value in buffer.iter_mut() {
        let magnitude = (value.re * value.re + value.im * value.im).sqrt();
        if magnitude < threshold {
            *value = Complex::new(0.0, 0.0);
        }
    }

    // Inverse FFT on columns
    let mut temp = vec![Complex::new(0.0, 0.0); size];
    for x in 0..width as usize {
        let mut column: Vec<Complex<f32>> = (0..height as usize)
            .map(|y| buffer[y * width as usize + x])
            .collect();
        
        let col_ifft = planner.plan_fft_inverse(height as usize);
        col_ifft.process(&mut column);
        
        for (y, &value) in column.iter().enumerate() {
            temp[y * width as usize + x] = value;
        }
    }
    *buffer = temp;

    // Inverse FFT on rows
    let row_ifft = planner.plan_fft_inverse(width as usize);
    for row in buffer.chunks_mut(width as usize) {
        row_ifft.process(row);
    }

    // Scale and return real components
    let scale_factor = 1.0 / (size as f32);
    Ok(buffer.iter().map(|c| c.re * scale_factor).collect())
}

/// Decompress a color image using FFT.
///
/// This function reads the compressed image and reconstructs the original image
/// using stored frequency information.
///
/// # Arguments
///
/// * `input_path` - A string slice that holds the file path of the compressed input image.
/// * `output_path` - A string slice that holds the file path to save the decompressed image.
///
/// # Example
/// ```python
/// fft_image_compression.decompress_image("compressed.png", "decompressed.png")
/// ```
#[pyfunction]
pub fn DecompressImageFFT(input_path: &str, output_path: &str) -> PyResult<()> {
    // Open image
    let img = match open(input_path) {
        Ok(img) => img.to_rgb8(),
        Err(err) => return Err(PyIOError::new_err(err.to_string())),
    };

    let (width, height) = img.dimensions();
    let size = (width * height) as usize;

    // Process each channel
    let mut red_channel: Vec<Complex<f32>> = Vec::with_capacity(size);
    let mut green_channel: Vec<Complex<f32>> = Vec::with_capacity(size);
    let mut blue_channel: Vec<Complex<f32>> = Vec::with_capacity(size);

    // Split into channels
    for pixel in img.pixels() {
        red_channel.push(Complex::new(pixel[0] as f32, 0.0));
        green_channel.push(Complex::new(pixel[1] as f32, 0.0));
        blue_channel.push(Complex::new(pixel[2] as f32, 0.0));
    }

    // Process each channel for decompression
    let decompressed_red = decompress_channel(&mut red_channel, width, height)?;
    let decompressed_green = decompress_channel(&mut green_channel, width, height)?;
    let decompressed_blue = decompress_channel(&mut blue_channel, width, height)?;

    // Combine channels back into an RGB image
    let mut output_img: RgbImage = ImageBuffer::new(width, height);
    for y in 0..height {
        for x in 0..width {
            let idx = (y * width + x) as usize;
            let red = decompressed_red[idx].max(0.0).min(255.0) as u8;
            let green = decompressed_green[idx].max(0.0).min(255.0) as u8;
            let blue = decompressed_blue[idx].max(0.0).min(255.0) as u8;
            output_img.put_pixel(x, y, Rgb([red, green, blue]));
        }
    }

    // Save the result
    if let Err(err) = output_img.save(output_path) {
        return Err(PyIOError::new_err(err.to_string()));
    }

    Ok(())
}

/// Helper function to decompress a single color channel
fn decompress_channel(
    buffer: &mut Vec<Complex<f32>>,
    width: u32,
    height: u32,
) -> PyResult<Vec<f32>> {
    let size = (width * height) as usize;
    let mut planner = FftPlanner::new();

    // FFT of compressed data
    let row_fft = planner.plan_fft_forward(width as usize);
    for row in buffer.chunks_mut(width as usize) {
        row_fft.process(row);
    }

    let mut temp = vec![Complex::new(0.0, 0.0); size];
    for x in 0..width as usize {
        let mut column: Vec<Complex<f32>> = (0..height as usize)
            .map(|y| buffer[y * width as usize + x])
            .collect();
        
        let col_fft = planner.plan_fft_forward(height as usize);
        col_fft.process(&mut column);
        
        for (y, &value) in column.iter().enumerate() {
            temp[y * width as usize + x] = value;
        }
    }
    *buffer = temp;

    // Inverse FFT
    let mut temp = vec![Complex::new(0.0, 0.0); size];
    for x in 0..width as usize {
        let mut column: Vec<Complex<f32>> = (0..height as usize)
            .map(|y| buffer[y * width as usize + x])
            .collect();
        
        let col_ifft = planner.plan_fft_inverse(height as usize);
        col_ifft.process(&mut column);
        
        for (y, &value) in column.iter().enumerate() {
            temp[y * width as usize + x] = value;
        }
    }
    *buffer = temp;

    let row_ifft = planner.plan_fft_inverse(width as usize);
    for row in buffer.chunks_mut(width as usize) {
        row_ifft.process(row);
    }

    // Scale and return real components
    let scale_factor = 1.0 / (size as f32);
    Ok(buffer.iter().map(|c| c.re * scale_factor).collect())
}