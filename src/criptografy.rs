use pyo3::prelude::*;
use num_bigint::BigUint;
use num_traits::{One, Zero};
use rand::Rng;

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

/*
GenerateRsaKeypair
EncryptRSA
DecryptRSA
EncryptAES
DecryptAES
*/


/// Educational implementation of RSA key pair generation.
/// WARNING: This is for learning purposes only and should NOT be used in production!
///
/// # Arguments
/// * `bits` - Desired key size in bits (ignored in this simplified version)
///
/// # Returns
/// * Tuple of strings (public_key, private_key), each formatted as "exponent,modulus"
///
/// # Example
/// ```python
/// public_key, private_key = GenerateRsaKeypair(2048)
/// # Returns something like ("65537,8675309...", "73924...,8675309...")
/// ```
///
/// # Security Notice
/// This implementation:
/// * Uses fixed prime numbers instead of generating random ones
/// * Lacks proper prime testing
/// * Has no padding scheme
/// * Is vulnerable to timing attacks
/// For production use, please use established libraries like RustCrypto#[pyfunction]
pub fn GenerateRsaKeypair(bits: u64) -> PyResult<(String, String)> {
    // Simple RSA key generation
    let mut rng = rand::thread_rng();
    
    // Generate two random prime numbers (simplified)
    let p = BigUint::from(65537u32); // Simplified - should be random prime
    let q = BigUint::from(65539u32); // Simplified - should be random prime
    
    // Calculate n = p * q
    let n = &p * &q;
    
    // Calculate φ(n) = (p-1)(q-1)
    let phi = (&p - BigUint::one()) * (&q - BigUint::one());
    
    // Choose public exponent e (commonly 65537)
    let e = BigUint::from(65537u32);
    
    // Calculate private exponent d
    let d = mod_inverse(&e, &phi).unwrap();
    
    // Return public and private keys as strings
    Ok((format!("{},{}", e, n), format!("{},{}", d, n)))
}


/// Encrypts a message using RSA public key encryption.
/// WARNING: Educational implementation only!
///
/// # Arguments
/// * `message` - Plain text message to encrypt
/// * `public_key` - RSA public key in the format "e,n" where e is the public exponent
///                  and n is the modulus
///
/// # Returns
/// * String containing the encrypted message as a decimal number
///
/// # Example
/// ```python
/// encrypted = EncryptRSA("Hello World", "65537,8675309...")
/// ```
///
/// # Security Notice
/// This implementation lacks:
/// * Proper padding (PKCS#1 v2.0 or OAEP)
/// * Message length validation
/// * Side-channel attack protection
/*
#[pyfunction]
pub fn EncryptRSA(message: &str, public_key: &str) -> PyResult<String> {
    // Parse public key
    let parts: Vec<&str> = public_key.split(',').collect();
    if parts.len() != 2 {
        return Err(PyErr::new::<pyo3::exceptions::PyValueError, _>("Invalid public key format"));
    }
    
    let e = parts[0].parse::<BigUint>().map_err(|_| 
        PyErr::new::<pyo3::exceptions::PyValueError, _>("Invalid public exponent"))?;
    let n = parts[1].parse::<BigUint>().map_err(|_| 
        PyErr::new::<pyo3::exceptions::PyValueError, _>("Invalid modulus"))?;
    
    // Convert message to number
    let m = message.bytes()
        .fold(BigUint::zero(), |acc, x| (acc << 8) + BigUint::from(x as u32));
    
    // Encrypt: c = m^e mod n
    let c = m.modpow(&e, &n);
    
    Ok(c.to_string())
}*/

/// Decrypts an RSA encrypted message using the private key.
/// WARNING: Educational implementation only!
///
/// # Arguments
/// * `ciphertext` - Encrypted message as decimal string
/// * `private_key` - RSA private key in the format "d,n" where d is the private exponent
///                   and n is the modulus
///
/// # Returns
/// * Decrypted message as string
///
/// # Example
/// ```python
/// decrypted = DecryptRSA(encrypted_message, "73924...,8675309...")
/// ```
///
/// # Security Notice
/// Lacks essential security features. Use established libraries for real applications.
/*
#[pyfunction]
pub fn DecryptRSA(ciphertext: &str, private_key: &str) -> PyResult<String> {
    // Parse private key
    let parts: Vec<&str> = private_key.split(',').collect();
    if parts.len() != 2 {
        return Err(PyErr::new::<pyo3::exceptions::PyValueError, _>("Invalid private key format"));
    }
    
    let d = parts[0].parse::<BigUint>().map_err(|_| 
        PyErr::new::<pyo3::exceptions::PyValueError, _>("Invalid private exponent"))?;
    let n = parts[1].parse::<BigUint>().map_err(|_| 
        PyErr::new::<pyo3::exceptions::PyValueError, _>("Invalid modulus"))?;
    
    // Parse ciphertext
    let c = ciphertext.parse::<BigUint>().map_err(|_| 
        PyErr::new::<pyo3::exceptions::PyValueError, _>("Invalid ciphertext"))?;
    
    // Decrypt: m = c^d mod n
    let m = c.modpow(&d, &n);
    
    // Convert number back to string
    let mut bytes = Vec::new();
    let mut temp = m;
    while temp > BigUint::zero() {
        // Use ToPrimitive trait to convert to u8
        let byte = (&temp % BigUint::from(256u32))
            .to_u8()
            .ok_or_else(|| PyErr::new::<pyo3::exceptions::PyValueError, _>("Conversion error"))?;
        bytes.push(byte);
        temp >>= 8;
    }
    bytes.reverse();
    
    String::from_utf8(bytes)
        .map_err(|_| PyErr::new::<pyo3::exceptions::PyValueError, _>("Invalid UTF-8 sequence"))
        .map_err(Into::into)
}
*/
/// Encrypts data using a simplified version of AES (Advanced Encryption Standard).
/// WARNING: This is a severely simplified version for educational purposes only!
///
/// # Arguments
/// * `data` - Plain text data to encrypt (max 16 bytes)
/// * `key` - Encryption key (should be 16 bytes)
///
/// # Returns
/// * Hex string of encrypted data
///
/// # Example
/// ```python
/// encrypted = aes_encrypt("Hello, World!", "MySixteenByteKey")
/// ```
///
/// # Security Notice
/// This implementation:
/// * Only performs one round (real AES uses 10-14 rounds)
/// * Has no proper key schedule
/// * Uses simplified S-box and MixColumns operations
/// * Lacks proper padding
/// * Has no initialization vector (IV)
/// * Does not implement proper block cipher modes
#[pyfunction]
pub fn EncryptAES(data: &str, key: &str) -> PyResult<String> {
    let mut state = [0u8; 16];
    let mut round_key = [0u8; 16];
    
    // Copy input data and key (simplified)
    for (i, byte) in data.bytes().take(16).enumerate() {
        state[i] = byte;
    }
    for (i, byte) in key.bytes().take(16).enumerate() {
        round_key[i] = byte;
    }
    
    // Simplified single round transformation
    add_round_key(&mut state, &round_key);
    sub_bytes(&mut state);
    shift_rows(&mut state);
    mix_columns(&mut state);
    add_round_key(&mut state, &round_key);
    
    // Convert result to hex string
    Ok(state.iter().map(|b| format!("{:02x}", b)).collect())
}

/// Decrypts data using simplified AES decryption.
/// WARNING: Educational implementation only!
///
/// # Arguments
/// * `ciphertext` - Hex string of encrypted data
/// * `key` - Decryption key (should be 16 bytes)
///
/// # Returns
/// * Decrypted string
///
/// # Example
/// ```python
/// decrypted = aes_decrypt(encrypted_hex_string, "MySixteenByteKey")
/// ```
///
/// # Security Notice
/// See encryption function for security limitations.

#[pyfunction]
pub fn DecryptAES(ciphertext: &str, key: &str) -> PyResult<String> {
    let mut state = [0u8; 16];
    let mut round_key = [0u8; 16];
    
    // Parse hex string input
    for i in 0..16 {
        state[i] = u8::from_str_radix(&ciphertext[i*2..i*2+2], 16).unwrap();
    }
    for (i, byte) in key.bytes().take(16).enumerate() {
        round_key[i] = byte;
    }
    
    // Simplified single round inverse transformation
    add_round_key(&mut state, &round_key);
    inv_mix_columns(&mut state);
    inv_shift_rows(&mut state);
    inv_sub_bytes(&mut state);
    add_round_key(&mut state, &round_key);
    
    // Convert back to string
    Ok(String::from_utf8(state.to_vec()).unwrap())
}

/// Represents a point on an elliptic curve for educational purposes.
///
/// # Fields
/// * `x` - X coordinate
/// * `y` - Y coordinate
///
/// # Security Notice
/// This is a basic implementation using integer arithmetic.
/// Real ECC uses finite field arithmetic and established curves.
#[pyclass]
struct ECPoint {
    x: i64,
    y: i64,
}

/// Adds two points on an elliptic curve y² = x³ + ax + b over field Fp.
/// WARNING: Simplified educational implementation!
///
/// # Arguments
/// * `p1` - First point as tuple (x, y)
/// * `p2` - Second point as tuple (x, y)
/// * `a` - Curve parameter a in y² = x³ + ax + b
/// * `p` - Field characteristic (prime number)
///
/// # Returns
/// * Resulting point as tuple (x, y)
///
/// # Example
/// ```python
/// result = EcPointAdd((2, 3), (4, 5), 2, 17)  # Points on curve y² = x³ + 2x over F17
/// ```
///
/// # Security Notice
/// This implementation:
/// * Uses simple integer arithmetic instead of proper finite field operations
/// * Does not validate that points are on the curve
/// * Has no protection against invalid curve attacks
/// * Is not constant-time
#[pyfunction]
pub fn EcPointAdd(p1: (i64, i64), p2: (i64, i64), a: i64, p: i64) -> PyResult<(i64, i64)> {
    if p1.0 == 0 && p1.1 == 0 {
        return Ok(p2);
    }
    if p2.0 == 0 && p2.1 == 0 {
        return Ok(p1);
    }
    
    let m = if p1.0 == p2.0 {
        if p1.1 == p2.1 {
            // Point doubling
            (3 * p1.0 * p1.0 + a) * mod_inverse_i64(2 * p1.1, p).unwrap() % p
        } else {
            // Vertical line
            return Ok((0, 0)); // Point at infinity
        }
    } else {
        // Point addition
        ((p2.1 - p1.1) * mod_inverse_i64(p2.0 - p1.0, p).unwrap()) % p
    };
    
    let x3 = (m * m - p1.0 - p2.0).rem_euclid(p);
    let y3 = (m * (p1.0 - x3) - p1.1).rem_euclid(p);
    
    Ok((x3, y3))
}

/// Helper function: Adds round key to the state matrix
///
/// # Arguments
/// * `state` - Current state matrix (16 bytes)
/// * `round_key` - Round key to add (16 bytes)
fn add_round_key(state: &mut [u8; 16], round_key: &[u8; 16]) {
    for i in 0..16 {
        state[i] ^= round_key[i];
    }
}

/// Helper function: Applies simplified S-box transformation
///
/// # Arguments
/// * `state` - State matrix to transform (16 bytes)
fn sub_bytes(state: &mut [u8; 16]) {
    // Simplified S-box (for demonstration)
    for i in 0..16 {
        state[i] = state[i].rotate_left(2) ^ 0x63;
    }
}

/// Helper function: Applies inverse S-box transformation
///
/// # Arguments
/// * `state` - State matrix to transform (16 bytes)
fn inv_sub_bytes(state: &mut [u8; 16]) {
    // Simplified inverse S-box
    for i in 0..16 {
        state[i] ^= 0x63;
        state[i] = state[i].rotate_right(2);
    }
}

/// Helper function: Shifts rows of the state matrix
///
/// # Arguments
/// * `state` - State matrix to transform (16 bytes)
fn shift_rows(state: &mut [u8; 16]) {
    let mut temp = *state;
    // Row 1
    state[1] = temp[5];
    state[5] = temp[9];
    state[9] = temp[13];
    state[13] = temp[1];
    // Row 2
    state[2] = temp[10];
    state[6] = temp[14];
    state[10] = temp[2];
    state[14] = temp[6];
    // Row 3
    state[3] = temp[15];
    state[7] = temp[3];
    state[11] = temp[7];
    state[15] = temp[11];
}
/// Helper function: Performs inverse shift rows operation
///
/// # Arguments
/// * `state` - State matrix to transform (16 bytes)
fn inv_shift_rows(state: &mut [u8; 16]) {
    let mut temp = *state;
    // Row 1
    state[1] = temp[13];
    state[5] = temp[1];
    state[9] = temp[5];
    state[13] = temp[9];
    // Row 2
    state[2] = temp[10];
    state[6] = temp[14];
    state[10] = temp[2];
    state[14] = temp[6];
    // Row 3
    state[3] = temp[7];
    state[7] = temp[11];
    state[11] = temp[15];
    state[15] = temp[3];
}
/// Helper function: Applies simplified MixColumns transformation
///
/// # Arguments
/// * `state` - State matrix to transform (16 bytes)
fn mix_columns(state: &mut [u8; 16]) {
    // Simplified MixColumns (for demonstration)
    for i in 0..4 {
        let col = [
            state[i*4], state[i*4 + 1],
            state[i*4 + 2], state[i*4 + 3]
        ];
        state[i*4] = col[0] ^ col[1];
        state[i*4 + 1] = col[1] ^ col[2];
        state[i*4 + 2] = col[2] ^ col[3];
        state[i*4 + 3] = col[3] ^ col[0];
    }
}
/// Helper function: Applies inverse MixColumns transformation
///
/// # Arguments
/// * `state` - State matrix to transform (16 bytes)
fn inv_mix_columns(state: &mut [u8; 16]) {
    // Simplified inverse MixColumns
    for i in 0..4 {
        let col = [
            state[i*4], state[i*4 + 1],
            state[i*4 + 2], state[i*4 + 3]
        ];
        state[i*4] = col[3] ^ col[0];
        state[i*4 + 1] = col[0] ^ col[1];
        state[i*4 + 2] = col[1] ^ col[2];
        state[i*4 + 3] = col[2] ^ col[3];
    }
}
/// Helper function: Calculates modular multiplicative inverse for BigUint
///
/// # Arguments
/// * `a` - Number to find inverse for
/// * `m` - Modulus
///
/// # Returns
/// * Option containing the modular multiplicative inverse if it exists
fn mod_inverse(a: &BigUint, m: &BigUint) -> Option<BigUint> {
    let mut t = (BigUint::zero(), BigUint::one());
    let mut r = (m.clone(), a.clone());
    
    while !r.1.is_zero() {
        let q = &r.0 / &r.1;
        t = (t.1.clone(), t.0 - &q * &t.1);
        r = (r.1.clone(), r.0 - &q * &r.1);
    }
    
    if r.0 > BigUint::one() {
        return None;
    }
    if t.0 < BigUint::zero() {
        t.0 = t.0 + m;
    }
    Some(t.0)
}

/// Helper function: Calculates modular multiplicative inverse for i64
///
/// # Arguments
/// * `a` - Number to find inverse for
/// * `m` - Modulus
///
/// # Returns
/// * Option containing the modular multiplicative inverse if it exists
fn mod_inverse_i64(a: i64, m: i64) -> Option<i64> {
    let mut t = (0i64, 1i64);
    let mut r = (m, a);
    
    while r.1 != 0 {
        let q = r.0 / r.1;
        t = (t.1, t.0 - q * t.1);
        r = (r.1, r.0 - q * r.1);
    }
    
    if r.0 > 1 {
        return None;
    }
    if t.0 < 0 {
        t.0 += m;
    }
    Some(t.0)
}