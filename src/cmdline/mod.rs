// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause
//
//! Helper for creating valid kernel command line strings.

use std::fmt;
use std::result;

/// The error type for command line building operations.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// Operation would have resulted in a non-printable ASCII character.
    InvalidAscii,
    /// Key/Value Operation would have had a space in it.
    HasSpace,
    /// Key/Value Operation would have had an equals sign in it.
    HasEquals,
    /// Operation would have made the command line too large.
    TooLarge,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match *self {
                Error::InvalidAscii => "String contains a non-printable ASCII character.",
                Error::HasSpace => "String contains a space.",
                Error::HasEquals => "String contains an equals sign.",
                Error::TooLarge => "Inserting string would make command line too long.",
            }
        )
    }
}

impl std::error::Error for Error {}

/// Specialized [`Result`] type for command line operations.
///
/// [`Result`]: https://doc.rust-lang.org/std/result/enum.Result.html
pub type Result<T> = result::Result<T, Error>;

fn valid_char(c: char) -> bool {
    match c {
        ' '..='~' => true,
        _ => false,
    }
}

fn valid_str(s: &str) -> Result<()> {
    if s.chars().all(valid_char) {
        Ok(())
    } else {
        Err(Error::InvalidAscii)
    }
}

fn valid_element(s: &str) -> Result<()> {
    if !s.chars().all(valid_char) {
        Err(Error::InvalidAscii)
    } else if s.contains(' ') {
        Err(Error::HasSpace)
    } else if s.contains('=') {
        Err(Error::HasEquals)
    } else {
        Ok(())
    }
}

/// A builder for a kernel command line string that validates the string as it's being built.
/// A `CString` can be constructed from this directly using `CString::new`.
///
/// # Examples
///
/// ```rust
/// # use linux_loader::cmdline::*;
/// # use std::ffi::CString;
/// let cl = Cmdline::new(100);
/// let cl_cstring = CString::new(cl).unwrap();
/// assert_eq!(cl_cstring.to_str().unwrap(), "");
/// ```
pub struct Cmdline {
    line: String,
    capacity: usize,
}

impl Cmdline {
    /// Constructs an empty [`Cmdline`] with the given capacity, including the nul terminator.
    ///
    /// # Arguments
    ///
    /// * `capacity` - Command line capacity. Must be greater than 0.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// let cl = Cmdline::new(100);
    /// ```
    /// [`Cmdline`]: struct.Cmdline.html
    pub fn new(capacity: usize) -> Cmdline {
        assert_ne!(capacity, 0);
        Cmdline {
            line: String::with_capacity(capacity),
            capacity,
        }
    }

    fn has_capacity(&self, more: usize) -> Result<()> {
        let needs_space = if self.line.is_empty() { 0 } else { 1 };
        if self.line.len() + more + needs_space < self.capacity {
            Ok(())
        } else {
            Err(Error::TooLarge)
        }
    }

    fn start_push(&mut self) {
        if !self.line.is_empty() {
            self.line.push(' ');
        }
    }

    fn end_push(&mut self) {
        // This assert is always true because of the `has_capacity` check that each insert method
        // uses.
        assert!(self.line.len() < self.capacity);
    }

    /// Validates and inserts a key-value pair into this command line.
    ///
    /// # Arguments
    ///
    /// * `key` - Key to be inserted in the command line string.
    /// * `val` - Value corresponding to `key`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// # use std::ffi::CString;
    /// let mut cl = Cmdline::new(100);
    /// cl.insert("foo", "bar");
    /// let cl_cstring = CString::new(cl).unwrap();
    /// assert_eq!(cl_cstring.to_str().unwrap(), "foo=bar");
    /// ```
    pub fn insert<T: AsRef<str>>(&mut self, key: T, val: T) -> Result<()> {
        let k = key.as_ref();
        let v = val.as_ref();

        valid_element(k)?;
        valid_element(v)?;
        self.has_capacity(k.len() + v.len() + 1)?;

        self.start_push();
        self.line.push_str(k);
        self.line.push('=');
        self.line.push_str(v);
        self.end_push();

        Ok(())
    }

    /// Validates and inserts a string to the end of the current command line.
    ///
    /// # Arguments
    ///
    /// * `slug` - String to be appended to the command line.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// # use std::ffi::CString;
    /// let mut cl = Cmdline::new(100);
    /// cl.insert_str("foobar");
    /// let cl_cstring = CString::new(cl).unwrap();
    /// assert_eq!(cl_cstring.to_str().unwrap(), "foobar");
    /// ```
    pub fn insert_str<T: AsRef<str>>(&mut self, slug: T) -> Result<()> {
        let s = slug.as_ref();
        valid_str(s)?;

        self.has_capacity(s.len())?;

        self.start_push();
        self.line.push_str(s);
        self.end_push();

        Ok(())
    }

    /// Returns the string representation of the command line without the nul terminator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// let mut cl = Cmdline::new(10);
    /// cl.insert_str("foobar");
    /// assert_eq!(cl.as_str(), "foobar");
    /// ```
    pub fn as_str(&self) -> &str {
        self.line.as_str()
    }
}

impl Into<Vec<u8>> for Cmdline {
    fn into(self) -> Vec<u8> {
        self.line.into_bytes()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

    #[test]
    fn test_insert_hello_world() {
        let mut cl = Cmdline::new(100);
        assert_eq!(cl.as_str(), "");
        assert!(cl.insert("hello", "world").is_ok());
        assert_eq!(cl.as_str(), "hello=world");

        let s = CString::new(cl).expect("failed to create CString from Cmdline");
        assert_eq!(s, CString::new("hello=world").unwrap());
    }

    #[test]
    fn test_insert_multi() {
        let mut cl = Cmdline::new(100);
        assert!(cl.insert("hello", "world").is_ok());
        assert!(cl.insert("foo", "bar").is_ok());
        assert_eq!(cl.as_str(), "hello=world foo=bar");
    }

    #[test]
    fn test_insert_space() {
        let mut cl = Cmdline::new(100);
        assert_eq!(cl.insert("a ", "b"), Err(Error::HasSpace));
        assert_eq!(cl.insert("a", "b "), Err(Error::HasSpace));
        assert_eq!(cl.insert("a ", "b "), Err(Error::HasSpace));
        assert_eq!(cl.insert(" a", "b"), Err(Error::HasSpace));
        assert_eq!(cl.as_str(), "");
    }

    #[test]
    fn test_insert_equals() {
        let mut cl = Cmdline::new(100);
        assert_eq!(cl.insert("a=", "b"), Err(Error::HasEquals));
        assert_eq!(cl.insert("a", "b="), Err(Error::HasEquals));
        assert_eq!(cl.insert("a=", "b "), Err(Error::HasEquals));
        assert_eq!(cl.insert("=a", "b"), Err(Error::HasEquals));
        assert_eq!(cl.insert("a", "=b"), Err(Error::HasEquals));
        assert_eq!(cl.as_str(), "");
    }

    #[test]
    fn test_insert_emoji() {
        let mut cl = Cmdline::new(100);
        assert_eq!(cl.insert("heart", "💖"), Err(Error::InvalidAscii));
        assert_eq!(cl.insert("💖", "love"), Err(Error::InvalidAscii));
        assert_eq!(cl.as_str(), "");
    }

    #[test]
    fn test_insert_string() {
        let mut cl = Cmdline::new(13);
        assert_eq!(cl.as_str(), "");
        assert!(cl.insert_str("noapic").is_ok());
        assert_eq!(cl.as_str(), "noapic");
        assert!(cl.insert_str("nopci").is_ok());
        assert_eq!(cl.as_str(), "noapic nopci");
    }

    #[test]
    fn test_insert_too_large() {
        let mut cl = Cmdline::new(4);
        assert_eq!(cl.insert("hello", "world"), Err(Error::TooLarge));
        assert_eq!(cl.insert("a", "world"), Err(Error::TooLarge));
        assert_eq!(cl.insert("hello", "b"), Err(Error::TooLarge));
        assert!(cl.insert("a", "b").is_ok());
        assert_eq!(cl.insert("a", "b"), Err(Error::TooLarge));
        assert_eq!(cl.insert_str("a"), Err(Error::TooLarge));
        assert_eq!(cl.as_str(), "a=b");

        let mut cl = Cmdline::new(10);
        assert!(cl.insert("ab", "ba").is_ok()); // adds 5 length
        assert_eq!(cl.insert("c", "da"), Err(Error::TooLarge)); // adds 5 (including space) length
        assert!(cl.insert("c", "d").is_ok()); // adds 4 (including space) length
    }
}
