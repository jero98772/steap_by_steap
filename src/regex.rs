use pyo3::prelude::*;

/// Represents a compiled regex pattern
pub struct RegexLocal {
    pattern: String,
}

impl RegexLocal {
    /// Creates a new Regex instance
    pub fn new(pattern: &str) -> Self {
        RegexLocal {
            pattern: pattern.to_string(),
        }
    }

    /// Checks if the pattern matches the text
    pub fn is_match(&self, text: &str) -> bool {
        self.match_here(&self.pattern, text)
    }

    /// Matches the pattern here
    fn match_here(&self, pattern: &str, text: &str) -> bool {
        if pattern.is_empty() {
            return true;
        }
        if pattern.len() > 1 && &pattern[1..2] == "*" {
            return self.match_star(&pattern[0..1], &pattern[2..], text);
        }
        if !text.is_empty() && (&pattern[0..1] == "." || pattern[0..1] == text[0..1]) {
            return self.match_here(&pattern[1..], &text[1..]);
        }
        false
    }

    /// Matches zero or more of the preceding element
    fn match_star(&self, char: &str, pattern: &str, text: &str) -> bool {
        let mut text_iter = text.chars();
        while let Some(c) = text_iter.next() {
            if self.match_here(pattern, &text[text_iter.as_str().len()..]) {
                return true;
            }
            if char != "." && char != &c.to_string() {
                return false;
            }
        }
        self.match_here(pattern, "")
    }
}

#[pyclass]
/// A compiled regular expression object
pub struct Regex {
    inner: RegexLocal,
}

#[pymethods]
impl Regex {
    #[new]
    /// Compile a regex pattern
    ///
    /// Args:
    ///     pattern (str): The regex pattern to compile
    ///
    /// Returns:
    ///     Regex: A compiled regex object
    fn new(pattern: &str) -> Self {
        Regex {
            inner: RegexLocal::new(pattern),
        }
    }

    /// Check if the regex pattern matches the text
    ///
    /// Args:
    ///     text (str): The text to match against
    ///
    /// Returns:
    ///     bool: True if the text matches the pattern, False otherwise
    fn is_match(&self, text: &str) -> bool {
        self.inner.is_match(text)
    }
}

