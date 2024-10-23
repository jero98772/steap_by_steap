use pyo3::prelude::*;

/// Simple XOR Encryption
///
/// # Arguments
/// * `data` - The binary string to encrypt
/// * `key` - A character used as the encryption key
///
/// # Returns
/// * Encrypted binary string
#[pyfunction]
pub fn EncryptXOR(data: &str, key: char) -> PyResult<String> {
    let encrypted: String = data
        .chars()
        .map(|ch| ((ch as u8) ^ (key as u8)) as char)
        .collect();
    Ok(encrypted)
}

/// Simple XOR Decryption
///
/// # Arguments
/// * `data` - The encrypted binary string
/// * `key` - A character used as the decryption key
///
/// # Returns
/// * Decrypted binary string
#[pyfunction]
pub fn DecryptXOR(data: &str, key: char) -> PyResult<String> {
    // XOR decryption works the same as encryption
    let decrypted: String = data
        .chars()
        .map(|ch| ((ch as u8) ^ (key as u8)) as char)
        .collect();
    Ok(decrypted)
}
