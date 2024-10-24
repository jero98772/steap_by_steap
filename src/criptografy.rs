use pyo3::prelude::*;
use pyo3::wrap_pyfunction;
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

// A constant for the character set
const CHARS: &str = " ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
fn is_prime(num: usize) -> bool {
    if num < 2 {
        return false;
    }
    for i in 2..=((num as f64).sqrt() as usize) {
        if num % i == 0 {
            return false;
        }
    }
    true
}
/// Generates a random prime number
///
/// # Arguments
/// * `limit` - The upper limit within which to find a prime number.
///
/// # Returns
/// * A random prime number within the specified limit.
///
/// # Example
/// ```python
/// prime = RandomPrime(100)
/// ```
fn get_random_prime(limit: usize) -> usize {
    let mut rng = rand::thread_rng();
    loop {
        let num = rng.gen_range(2..=limit);
        if is_prime(num) {
            return num;
        }
    }
}

// Function to compute the GCD
fn gcd(a: usize, b: usize) -> usize {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

// Public key generation
fn public_key_e(fi: usize) -> usize {
    for i in 2..fi {
        if gcd(fi, i) == 1 {
            return i;
        }
    }
    0
}

// Private key generation
fn private_key_d(e: usize, fi: usize) -> usize {
    let mut i = 2;
    loop {
        let formula = (1 + fi * i) % e;
        let d = (1 + fi * i) / e;
        if formula == 0 && d != e {
            return d;
        }
        i += 1;
    }
}

/// Generates RSA keys
///
/// Given two prime numbers, this function generates the RSA public and private keys.
///
/// # Arguments
/// * `key1` - The first prime number.
/// * `key2` - The second prime number.
///
/// # Returns
/// * A tuple `(n, e, d)` where `n` is the modulus, `e` is the public key exponent, and `d` is the private key exponent.
///
/// # Example
/// ```python
/// n, e, d = GenerateKey(61, 53)
/// ```
fn gen_key(key1: usize, key2: usize) -> (usize, usize, usize) {
    let n = key1 * key2;
    let fi = (key1 - 1) * (key2 - 1);
    let e = public_key_e(fi);
    let d = private_key_d(e, fi);
    (n, e, d)
}

/// RSA Encryption
///
/// Encrypts a message using the RSA encryption scheme.
///
/// # Arguments
/// * `msg` - The message to encrypt.
/// * `e` - The public key exponent.
/// * `n` - The modulus.
///
/// # Returns
/// * Encrypted message as a list of numbers.
///
/// # Example
/// ```python
/// encrypted_msg = EncryptRSA("HELLO", e, n)
/// ```
fn encrypt_rsa(msg: &str, e: usize, n: usize) -> Vec<usize> {
    msg.chars()
        .map(|c| {
            let value = CHARS.find(c).unwrap();
            (value.pow(e as u32)) % n
        })
        .collect()
}

/// RSA Decryption
///
/// Decrypts a message encrypted with RSA.
///
/// # Arguments
/// * `cifrate` - The encrypted message as a list of numbers.
/// * `d` - The private key exponent.
/// * `n` - The modulus.
///
/// # Returns
/// * Decrypted message as a string.
///
/// # Example
/// ```python
/// decrypted_msg = DecryptRSA(encrypted_msg, d, n)
/// ```
fn decrypt_rsa(cifrate: &[usize], d: usize, n: usize) -> String {
    cifrate
        .iter()
        .map(|&value| {
            let dechar = (value.pow(d as u32)) % n;
            CHARS.chars().nth(dechar).unwrap()
        })
        .collect()
}

#[pyfunction]
pub fn RandomPrime(limit: usize) -> usize {
    get_random_prime(limit)
}

#[pyfunction]
pub fn GenerateKey(key1: usize, key2: usize) -> (usize, usize, usize) {
    gen_key(key1, key2)
}

#[pyfunction]
pub fn EncryptRSA(msg: &str, e: usize, n: usize) -> Vec<usize> {
    encrypt_rsa(msg, e, n)
}

#[pyfunction]
pub fn DecryptRSA(cifrate: Vec<usize>, d: usize, n: usize) -> String {
    decrypt_rsa(&cifrate, d, n)
}


/// Caesar Cipher Encryption
///
/// Encrypts the input text using Caesar cipher with a given shift.
///
/// # Arguments
/// * `text` - The input text to encrypt.
/// * `shift` - The number of positions to shift characters.
///
/// # Returns
/// * The encrypted text.
///
/// # Example
/// ```python
/// encrypted = EncryptCesar("HELLO", 3)
/// ```
#[pyfunction]
pub fn EncryptCesar(text: &str, shift: usize) -> String {
    let mut encrypted = String::new();
    for c in text.chars() {
        let encrypted_char = match c {
            'A'..='Z' => {
                let base = 'A' as u8;
                let new_char = ((c as u8 - base + shift as u8) % 26 + base) as char;
                new_char
            }
            'a'..='z' => {
                let base = 'a' as u8;
                let new_char = ((c as u8 - base + shift as u8) % 26 + base) as char;
                new_char
            }
            _ => c,
        };
        encrypted.push(encrypted_char);
    }
    encrypted
}



/// Caesar Cipher Decryption
///
/// Decrypts the input text encrypted with Caesar cipher using a given shift.
///
/// # Arguments
/// * `text` - The encrypted text.
/// * `shift` - The number of positions the characters were shifted.
///
/// # Returns
/// * The decrypted text.
///
/// # Example
/// ```python
/// decrypted = DecryptCesar(encrypted, 3)
/// ```
#[pyfunction]
pub fn DecryptCesar(text: &str, shift: usize) -> String {
    EncryptCesar(text, 26 - shift)
}

/// Rail Fence Cipher Encryption
///
/// Encrypts the input text using Rail Fence cipher with a given number of rails.
///
/// # Arguments
/// * `text` - The input text to encrypt.
/// * `rails` - The number of rails to use in the cipher.
///
/// # Returns
/// * The encrypted text.
///
/// # Example
/// ```python
/// encrypted = EncryptRailFence("HELLO", 3)
/// ```
#[pyfunction]
pub fn EncryptRailFence(text: &str, rails: usize) -> String {
    if rails == 0 {
        return text.to_string(); // Return the text as-is if no rails are specified
    }

    let mut rail = vec![String::new(); rails];
    let mut direction_down = false;
    let mut row: isize = 0; // Change to isize for row

    for c in text.chars() {
        rail[row as usize].push(c); // Cast row to usize
        if row == 0 || row == (rails as isize) - 1 {
            direction_down = !direction_down;
        }
        row += if direction_down { 1 } else { -1 };
    }

    rail.concat()
}

///
/// Decrypts the input text encrypted using Rail Fence cipher with a given number of rails.
///
/// # Arguments
/// * `text` - The encrypted text.
/// * `rails` - The number of rails used in the cipher.
///
/// # Returns
/// * The decrypted text.
///
/// # Example
/// ```python
/// decrypted = DecryptRailFence(encrypted, 3)
/// ```
#[pyfunction]
pub fn DecryptRailFence(text: &str, rails: usize) -> String {
    let len = text.len();
    if rails == 0 {
        return text.to_string(); // Return the text as-is if no rails are specified
    }

    let mut rail = vec![vec!['\0'; len]; rails];
    let mut direction_down = false;
    let mut row: isize = 0; // Change to isize for row

    // Mark the positions of the rails
    for i in 0..len {
        if row == 0 {
            direction_down = true;
        } else if row == (rails as isize) - 1 {
            direction_down = false;
        }
        rail[row as usize][i] = '*'; // Cast row to usize
        row += if direction_down { 1 } else { -1 };
    }

    // Fill the marked positions with characters from the text
    let mut index = 0;
    for r in 0..rails {
        for c in 0..len {
            if rail[r][c] == '*' {
                rail[r][c] = text.chars().nth(index).unwrap();
                index += 1;
            }
        }
    }

    // Read the characters in a zigzag manner
    let mut decrypted = String::new();
    row = 0;
    for i in 0..len {
        decrypted.push(rail[row as usize][i]); // Cast row to usize
        if row == 0 {
            direction_down = true;
        } else if row == (rails as isize) - 1 {
            direction_down = false;
        }
        row += if direction_down { 1 } else { -1 };
    }

    decrypted
}