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

use vm_memory::{Address, GuestAddress, GuestUsize};

/// The error type for command line building operations.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// Operation would have resulted in a non-printable ASCII character.
    InvalidAscii,
    /// Invalid device passed to the kernel command line builder.
    InvalidDevice(String),
    /// Key/Value Operation would have had a space in it.
    HasSpace,
    /// Key/Value Operation would have had an equals sign in it.
    HasEquals,
    /// Key/Value Operation was not passed a value.
    MissingVal(String),
    /// 0-sized virtio MMIO device passed to the kernel command line builder.
    MmioSize,
    /// Operation would have made the command line too large.
    TooLarge,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::InvalidAscii => write!(f, "String contains a non-printable ASCII character."),
            Error::InvalidDevice(ref dev) => write!(
                f,
                "Invalid device passed to the kernel command line builder: {}.",
                dev
            ),
            Error::HasSpace => write!(f, "String contains a space."),
            Error::HasEquals => write!(f, "String contains an equals sign."),
            Error::MissingVal(ref k) => write!(f, "Missing value for key {}.", k),
            Error::MmioSize => write!(
                f,
                "0-sized virtio MMIO device passed to the kernel command line builder."
            ),
            Error::TooLarge => write!(f, "Inserting string would make command line too long."),
        }
    }
}

impl std::error::Error for Error {}

/// Specialized [`Result`] type for command line operations.
///
/// [`Result`]: https://doc.rust-lang.org/std/result/enum.Result.html
pub type Result<T> = result::Result<T, Error>;

fn valid_char(c: char) -> bool {
    matches!(c, ' '..='~')
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
    // The commandline is split into two regions (as per the documentation:
    // https://www.kernel.org/doc/html/latest/admin-guide/kernel-parameters.html):
    // * the first region contains the regular parameters
    // * the last regions contains the init parameters
    // We need this so that we can ensure that the init parameters always stay at the end
    // of the commandline.
    region_delim: usize,
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
            region_delim: 0,
            capacity,
        }
    }

    fn regular_needed_space(&self) -> usize {
        // We calculate how much space we need for altering the regular params region
        // of the commandline. We only need to account for the need of a space before
        // upon inserting another regular param.
        if self.region_delim == 0 {
            0
        } else {
            1
        }
    }

    fn init_needed_space(&self) -> usize {
        // We calculate how much space we need for altering the init params region
        // of the commandline. We also need to take into account the presence of "--".

        // Since the init params lies in the second region of
        // the commandline, we always need a space.
        let mut space_needed = 1;
        if !self.line.contains("--") {
            space_needed += 3;
        }
        space_needed
    }

    fn has_capacity(&self, more: usize) -> Result<()> {
        if self.line.len() + more < self.capacity {
            Ok(())
        } else {
            Err(Error::TooLarge)
        }
    }

    fn start_regular_push(&mut self) {
        if self.region_delim > 0 {
            self.line.insert(self.region_delim, ' ');
            self.region_delim += 1;
        }
    }

    fn start_init_push(&mut self) {
        if !self.line.contains("--") {
            self.line.push_str(" --");
        }
        self.line.push(' ');
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
        let pair = format!("{}={}", k, v);

        self.has_capacity(pair.len() + self.regular_needed_space())?;

        self.start_regular_push();
        self.line.insert_str(self.region_delim, &pair);
        self.end_push();

        self.region_delim += pair.len();

        Ok(())
    }

    /// Validates and inserts a key-value1,...,valueN pair into this command line.
    ///
    /// # Arguments
    ///
    /// * `key` - Key to be inserted in the command line string.
    /// * `vals` - Values corresponding to `key`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// # use std::ffi::CString;
    /// let mut cl = Cmdline::new(100);
    /// cl.insert_multiple("foo", &["bar", "baz"]);
    /// let cl_cstring = CString::new(cl).unwrap();
    /// assert_eq!(cl_cstring.to_str().unwrap(), "foo=bar,baz");
    /// ```
    pub fn insert_multiple<T: AsRef<str>>(&mut self, key: T, vals: &[T]) -> Result<()> {
        let k = key.as_ref();

        valid_element(k)?;
        if vals.is_empty() {
            return Err(Error::MissingVal(k.to_string()));
        }

        let kv_str = format!(
            "{}={}",
            k,
            vals.iter()
                .map(|v| -> Result<&str> {
                    valid_element(v.as_ref())?;
                    Ok(v.as_ref())
                })
                .collect::<Result<Vec<&str>>>()?
                .join(",")
        );

        self.insert_str(kv_str)
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

        self.has_capacity(s.len() + self.regular_needed_space())?;

        self.start_regular_push();
        self.line.insert_str(self.region_delim, s);
        self.end_push();

        self.region_delim += s.len();

        Ok(())
    }

    /// Validates and inserts a string to the init params region of the command line.
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
    /// cl.insert_str("/bin/ls");
    /// cl.insert_init_args("/etc/shadow");
    /// let cl_cstring = CString::new(cl).unwrap();
    /// assert_eq!(cl_cstring.to_str().unwrap(), "/bin/ls -- /etc/shadow");
    /// ```
    pub fn insert_init_args<T: AsRef<str>>(&mut self, slug: T) -> Result<()> {
        let s = slug.as_ref();
        valid_str(s)?;

        self.has_capacity(s.len() + self.init_needed_space())?;

        self.start_init_push();
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

    /// Adds a virtio MMIO device to the kernel command line.
    ///
    /// Multiple devices can be specified, with multiple `virtio_mmio.device=` options. This
    /// function must be called once per device.
    /// The function appends a string of the following format to the kernel command line:
    /// `<size>@<baseaddr>:<irq>[:<id>]`.
    /// For more details see the [documentation] (section `virtio_mmio.device=`).
    ///
    /// # Arguments
    ///
    /// * `size` - size of the slot the device occupies on the MMIO bus.
    /// * `baseaddr` - physical base address of the device.
    /// * `irq` - interrupt number to be used by the device.
    /// * `id` - optional platform device ID.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use linux_loader::cmdline::*;
    /// # use std::ffi::CString;
    /// # use vm_memory::{GuestAddress, GuestUsize};
    /// let mut cl = Cmdline::new(100);
    /// cl.add_virtio_mmio_device(1 << 12, GuestAddress(0x1000), 5, Some(42)).unwrap();
    /// let cl_cstring = CString::new(cl).unwrap();
    /// assert_eq!(cl_cstring.to_str().unwrap(), "virtio_mmio.device=4K@0x1000:5:42");
    /// ```
    ///
    /// [documentation]: https://www.kernel.org/doc/html/latest/admin-guide/kernel-parameters.html
    pub fn add_virtio_mmio_device(
        &mut self,
        size: GuestUsize,
        baseaddr: GuestAddress,
        irq: u32,
        id: Option<u32>,
    ) -> Result<()> {
        if size == 0 {
            return Err(Error::MmioSize);
        }

        let mut device_str = format!(
            "virtio_mmio.device={}@0x{:x?}:{}",
            Self::guestusize_to_str(size),
            baseaddr.raw_value(),
            irq
        );
        if let Some(id) = id {
            device_str.push_str(format!(":{}", id).as_str());
        }
        self.insert_str(&device_str)
    }

    // Converts a `GuestUsize` to a concise string representation, with multiplier suffixes.
    fn guestusize_to_str(size: GuestUsize) -> String {
        const KB_MULT: u64 = 1 << 10;
        const MB_MULT: u64 = KB_MULT << 10;
        const GB_MULT: u64 = MB_MULT << 10;

        if size % GB_MULT == 0 {
            return format!("{}G", size / GB_MULT);
        }
        if size % MB_MULT == 0 {
            return format!("{}M", size / MB_MULT);
        }
        if size % KB_MULT == 0 {
            return format!("{}K", size / KB_MULT);
        }
        size.to_string()
    }
}

impl From<Cmdline> for Vec<u8> {
    fn from(cmdline: Cmdline) -> Vec<u8> {
        cmdline.line.into_bytes()
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

    #[test]
    fn test_insert_init_args() {
        let mut cl = Cmdline::new(100);
        assert!(cl.insert("init", "/bin/ls").is_ok());
        assert!(cl.insert_init_args("/etc/passwd").is_ok());
        assert_eq!(cl.as_str(), "init=/bin/ls -- /etc/passwd");
        assert!(cl.insert_str("pci").is_ok());
        assert_eq!(cl.as_str(), "init=/bin/ls pci -- /etc/passwd");

        assert!(cl.insert("root", "/dev/vda").is_ok());
        assert_eq!(cl.as_str(), "init=/bin/ls pci root=/dev/vda -- /etc/passwd");
        assert!(cl.insert_init_args("/etc/profile").is_ok());
        assert_eq!(
            cl.as_str(),
            "init=/bin/ls pci root=/dev/vda -- /etc/passwd /etc/profile"
        );
    }

    #[test]
    fn test_add_virtio_mmio_device() {
        let mut cl = Cmdline::new(5);
        assert_eq!(
            cl.add_virtio_mmio_device(0, GuestAddress(0), 0, None),
            Err(Error::MmioSize)
        );
        assert_eq!(
            cl.add_virtio_mmio_device(1, GuestAddress(0), 0, None),
            Err(Error::TooLarge)
        );

        let mut cl = Cmdline::new(150);
        assert!(cl
            .add_virtio_mmio_device(1, GuestAddress(0), 1, None)
            .is_ok());
        let mut expected_str = "virtio_mmio.device=1@0x0:1".to_string();
        assert_eq!(cl.as_str(), &expected_str);

        assert!(cl
            .add_virtio_mmio_device(2 << 10, GuestAddress(0x100), 2, None)
            .is_ok());
        expected_str.push_str(" virtio_mmio.device=2K@0x100:2");
        assert_eq!(cl.as_str(), &expected_str);

        assert!(cl
            .add_virtio_mmio_device(3 << 20, GuestAddress(0x1000), 3, None)
            .is_ok());
        expected_str.push_str(" virtio_mmio.device=3M@0x1000:3");
        assert_eq!(cl.as_str(), &expected_str);

        assert!(cl
            .add_virtio_mmio_device(4 << 30, GuestAddress(0x0001_0000), 4, Some(42))
            .is_ok());
        expected_str.push_str(" virtio_mmio.device=4G@0x10000:4:42");
        assert_eq!(cl.as_str(), &expected_str);
    }

    #[test]
    fn test_insert_kv() {
        let mut cl = Cmdline::new(10);

        let no_vals: Vec<&str> = vec![];
        assert_eq!(cl.insert_multiple("foo=", &no_vals), Err(Error::HasEquals));
        assert_eq!(
            cl.insert_multiple("foo", &no_vals),
            Err(Error::MissingVal("foo".to_string()))
        );
        assert_eq!(cl.insert_multiple("foo", &["bar "]), Err(Error::HasSpace));
        assert_eq!(
            cl.insert_multiple("foo", &["bar", "baz"]),
            Err(Error::TooLarge)
        );

        let mut cl = Cmdline::new(100);
        assert!(cl.insert_multiple("foo", &["bar"]).is_ok());
        assert_eq!(cl.as_str(), "foo=bar");

        let mut cl = Cmdline::new(100);
        assert!(cl.insert_multiple("foo", &["bar", "baz"]).is_ok());
        assert_eq!(cl.as_str(), "foo=bar,baz");
    }
}
