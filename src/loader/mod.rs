// Copyright © 2020, Oracle and/or its affiliates.
//
// Copyright (c) 2019 Intel Corporation. All rights reserved.
// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

//! Traits and Structs for loading kernels into guest memory.
//! - [KernelLoader](trait.KernelLoader.html): load kernel image into guest memory
//! - [KernelLoaderResult](struct.KernelLoaderResult.html): the structure which loader
//! returns to VMM to assist zero page construction and boot environment setup
//! - [Elf](struct.Elf.html): elf image loader
//! - [BzImage](struct.BzImage.html): bzImage loader

extern crate vm_memory;

use std::error::Error as StdError;
use std::ffi::CStr;
use std::fmt::{self, Display};
use std::io::{Read, Seek};

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use vm_memory::ByteValued;
use vm_memory::{Address, Bytes, GuestAddress, GuestMemory, GuestUsize};

#[allow(dead_code)]
#[allow(non_camel_case_types)]
#[allow(non_snake_case)]
#[allow(non_upper_case_globals)]
#[allow(missing_docs)]
#[cfg_attr(feature = "cargo-clippy", allow(clippy::all))]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub mod bootparam;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod x86_64;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub use x86_64::*;

#[cfg(target_arch = "aarch64")]
mod aarch64;
#[cfg(target_arch = "aarch64")]
pub use aarch64::*;

#[derive(Debug, PartialEq)]
/// Kernel loader errors.
pub enum Error {
    /// Failed to load bzimage.
    #[cfg(all(feature = "bzimage", any(target_arch = "x86", target_arch = "x86_64")))]
    Bzimage(bzimage::Error),

    /// Failed to load elf image.
    #[cfg(all(feature = "elf", any(target_arch = "x86", target_arch = "x86_64")))]
    Elf(elf::Error),

    /// Failed to load PE image.
    #[cfg(all(feature = "pe", target_arch = "aarch64"))]
    Pe(pe::Error),

    /// Failed writing command line to guest memory.
    CommandLineCopy,
    /// Command line overflowed guest memory.
    CommandLineOverflow,
    /// Invalid kernel start address.
    InvalidKernelStartAddress,
    /// Memory to load kernel image is too small.
    MemoryOverflow,
}

/// A specialized `Result` type for the kernel loader.
pub type Result<T> = std::result::Result<T, Error>;

impl StdError for Error {
    fn description(&self) -> &str {
        match self {
            #[cfg(all(feature = "bzimage", any(target_arch = "x86", target_arch = "x86_64")))]
            Error::Bzimage(ref e) => e.description(),
            #[cfg(all(feature = "elf", any(target_arch = "x86", target_arch = "x86_64")))]
            Error::Elf(ref e) => e.description(),
            #[cfg(all(feature = "pe", target_arch = "aarch64"))]
            Error::Pe(ref e) => e.description(),

            Error::CommandLineCopy => "Failed writing command line to guest memory",
            Error::CommandLineOverflow => "Command line overflowed guest memory",
            Error::InvalidKernelStartAddress => "Invalid kernel start address",
            Error::MemoryOverflow => "Memory to load kernel image is not enough",
        }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Kernel Loader Error: {}", Error::description(self))
    }
}

#[cfg(all(feature = "elf", any(target_arch = "x86", target_arch = "x86_64")))]
impl From<elf::Error> for Error {
    fn from(err: elf::Error) -> Self {
        Error::Elf(err)
    }
}

#[cfg(all(feature = "bzimage", any(target_arch = "x86", target_arch = "x86_64")))]
impl From<bzimage::Error> for Error {
    fn from(err: bzimage::Error) -> Self {
        Error::Bzimage(err)
    }
}

#[cfg(all(feature = "pe", target_arch = "aarch64"))]
impl From<pe::Error> for Error {
    fn from(err: pe::Error) -> Self {
        Error::Pe(err)
    }
}

/// Result of [`KernelLoader.load()`](trait.KernelLoader.html#tymethod.load).
///
/// This specifies where the kernel is loading and passes additional
/// information for the rest of the boot process to be completed by
/// the VMM.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct KernelLoaderResult {
    /// Address in the guest memory where the kernel image starts to be loaded
    pub kernel_load: GuestAddress,
    /// Offset in guest memory corresponding to the end of kernel image, in case that
    /// device tree blob and initrd will be loaded adjacent to kernel image.
    pub kernel_end: GuestUsize,
    /// This field is only for bzImage following https://www.kernel.org/doc/Documentation/x86/boot.txt
    /// VMM should make use of it to fill zero page for bzImage direct boot.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    pub setup_header: Option<bootparam::setup_header>,
    /// This field optionally holds the address of a PVH entry point, indicating that
    /// the kernel supports the PVH boot protocol as described in:
    /// https://xenbits.xen.org/docs/unstable/misc/pvh.html
    pub pvh_entry_addr: Option<GuestAddress>,
}

/// A kernel image loading support must implement the KernelLoader trait.
/// The only method to be implemented is the load one, returning a KernelLoaderResult structure.
pub trait KernelLoader {
    /// How to load a specific kernel image format into the guest memory.
    fn load<F, M: GuestMemory>(
        guest_mem: &M,
        kernel_start: Option<GuestAddress>,
        kernel_image: &mut F,
        highmem_start_address: Option<GuestAddress>,
    ) -> Result<KernelLoaderResult>
    where
        F: Read + Seek;
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
unsafe impl ByteValued for bootparam::setup_header {}
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
unsafe impl ByteValued for bootparam::boot_params {}

/// Writes the command line string to the given guest memory slice.
///
/// # Arguments
///
/// * `guest_mem` - A u8 slice that will be partially overwritten by the command line.
/// * `guest_addr` - The address in `guest_mem` at which to load the command line.
/// * `cmdline` - The kernel command line.
pub fn load_cmdline<M: GuestMemory>(
    guest_mem: &M,
    guest_addr: GuestAddress,
    cmdline: &CStr,
) -> Result<()> {
    let len = cmdline.to_bytes().len();
    if len == 0 {
        return Ok(());
    }

    let end = guest_addr
        .checked_add(len as u64 + 1)
        .ok_or(Error::CommandLineOverflow)?; // Extra for null termination.
    if end > guest_mem.last_addr() {
        return Err(Error::CommandLineOverflow);
    }

    guest_mem
        .write_slice(cmdline.to_bytes_with_nul(), guest_addr)
        .map_err(|_| Error::CommandLineCopy)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use vm_memory::{Address, GuestAddress, GuestMemoryMmap};

    const MEM_SIZE: u64 = 0x100_0000;

    fn create_guest_mem() -> GuestMemoryMmap {
        GuestMemoryMmap::from_ranges(&[(GuestAddress(0x0), (MEM_SIZE as usize))]).unwrap()
    }

    #[test]
    fn cmdline_overflow() {
        let gm = create_guest_mem();
        let cmdline_address = GuestAddress(MEM_SIZE - 5);
        assert_eq!(
            Err(Error::CommandLineOverflow),
            load_cmdline(
                &gm,
                cmdline_address,
                CStr::from_bytes_with_nul(b"12345\0").unwrap()
            )
        );
    }

    #[test]
    fn cmdline_write_end() {
        let gm = create_guest_mem();
        let mut cmdline_address = GuestAddress(45);
        assert_eq!(
            Ok(()),
            load_cmdline(
                &gm,
                cmdline_address,
                CStr::from_bytes_with_nul(b"1234\0").unwrap()
            )
        );
        let val: u8 = gm.read_obj(cmdline_address).unwrap();
        assert_eq!(val, '1' as u8);
        cmdline_address = cmdline_address.unchecked_add(1);
        let val: u8 = gm.read_obj(cmdline_address).unwrap();
        assert_eq!(val, '2' as u8);
        cmdline_address = cmdline_address.unchecked_add(1);
        let val: u8 = gm.read_obj(cmdline_address).unwrap();
        assert_eq!(val, '3' as u8);
        cmdline_address = cmdline_address.unchecked_add(1);
        let val: u8 = gm.read_obj(cmdline_address).unwrap();
        assert_eq!(val, '4' as u8);
        cmdline_address = cmdline_address.unchecked_add(1);
        let val: u8 = gm.read_obj(cmdline_address).unwrap();
        assert_eq!(val, '\0' as u8);
    }
}
