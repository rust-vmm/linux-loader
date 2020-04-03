// Copyright (c) 2019 Intel Corporation. All rights reserved.
// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

//! Traits and structs for loading bzimage kernels into guest memory.

#![cfg(all(feature = "bzimage", any(target_arch = "x86", target_arch = "x86_64")))]

use std::error::{self, Error as StdError};
use std::fmt::{self, Display};
use std::io::{Read, Seek, SeekFrom};
use std::mem;

use vm_memory::{Address, ByteValued, Bytes, GuestAddress, GuestMemory, GuestUsize};

use super::super::{
    bootparam, Error as KernelLoaderError, KernelLoader, KernelLoaderResult, Result,
};

#[derive(Debug, PartialEq)]
/// Bzimage kernel loader errors.
pub enum Error {
    /// Invalid bzImage binary.
    InvalidBzImage,
    /// Unable to read bzImage header.
    ReadBzImageHeader,
    /// Unable to read bzImage compressed image.
    ReadBzImageCompressedKernel,
    /// Unable to seek to bzImage end.
    SeekBzImageEnd,
    /// Unable to seek to bzImage header.
    SeekBzImageHeader,
    /// Unable to seek to bzImage compressed kernel.
    SeekBzImageCompressedKernel,
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match self {
            Error::InvalidBzImage => "Invalid bzImage",
            Error::ReadBzImageHeader => "Unable to read bzImage header",
            Error::ReadBzImageCompressedKernel => "Unable to read bzImage compressed kernel",
            Error::SeekBzImageEnd => "Unable to seek bzImage end",
            Error::SeekBzImageHeader => "Unable to seek bzImage header",
            Error::SeekBzImageCompressedKernel => "Unable to seek bzImage compressed kernel",
        }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Kernel Loader Error: {}", self.description())
    }
}

/// Big zImage (bzImage) kernel image support.
pub struct BzImage;

impl KernelLoader for BzImage {
    /// Loads a kernel from a bzImage to guest memory.
    ///
    /// The kernel is loaded at `code32_start`, the default load address stored in the bzImage
    /// setup header.
    ///
    /// # Arguments
    ///
    /// * `guest_mem`: [`GuestMemory`] to load the kernel in.
    /// * `kernel_start`: Address in guest memory where the kernel is loaded.
    /// * `kernel_image` - Input bzImage image.
    /// * `highmem_start_address`: Address where high memory starts.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # extern crate vm_memory;
    /// # use linux_loader::loader::*;
    /// # use vm_memory::{Address, GuestAddress, GuestMemoryMmap};
    /// # use std::io::Cursor;
    /// let mem_size: usize = 0x1000000;
    /// let himem_start = GuestAddress(0x0);
    /// let kernel_addr = GuestAddress(0x200000);
    /// let gm = GuestMemoryMmap::from_ranges(&[(GuestAddress(0x0), mem_size)]).unwrap();
    /// let mut kernel_image = vec![];
    /// kernel_image.extend_from_slice(include_bytes!("bzimage"));
    /// bzimage::BzImage::load(
    ///     &gm,
    ///     Some(kernel_addr),
    ///     &mut Cursor::new(&kernel_image),
    ///     Some(himem_start),
    /// ).unwrap();
    /// ```
    ///
    /// [`GuestMemory`]: https://docs.rs/vm-memory/latest/vm_memory/guest_memory/trait.GuestMemory.html
    fn load<F, M: GuestMemory>(
        guest_mem: &M,
        kernel_start: Option<GuestAddress>,
        kernel_image: &mut F,
        highmem_start_address: Option<GuestAddress>,
    ) -> Result<KernelLoaderResult>
    where
        F: Read + Seek,
    {
        let mut kernel_size = kernel_image
            .seek(SeekFrom::End(0))
            .map_err(|_| Error::SeekBzImageEnd)? as usize;
        kernel_image
            .seek(SeekFrom::Start(0x1F1))
            .map_err(|_| Error::SeekBzImageHeader)?;

        let mut boot_header = bootparam::setup_header::default();
        boot_header
            .as_bytes()
            .read_from(0, kernel_image, mem::size_of::<bootparam::setup_header>())
            .map_err(|_| Error::ReadBzImageHeader)?;

        // If the `HdrS` magic number is not found at offset 0x202, the boot protocol version is
        // "old", the image type is assumed as zImage, not bzImage.
        if boot_header.header != 0x5372_6448 {
            Err(Error::InvalidBzImage)?;
        }

        // Follow the section related to loading the rest of the kernel in the linux boot protocol.
        if (boot_header.version < 0x0200) || ((boot_header.loadflags & 0x1) == 0x0) {
            Err(Error::InvalidBzImage)?;
        }

        let mut setup_size = boot_header.setup_sects as usize;
        if setup_size == 0 {
            setup_size = 4;
        }
        setup_size = (setup_size + 1) * 512;
        kernel_size -= setup_size;

        // Check that `code32_start`, the default address of the kernel, is not lower than high
        // memory.
        if (highmem_start_address.is_some())
            && (u64::from(boot_header.code32_start) < highmem_start_address.unwrap().raw_value())
        {
            return Err(KernelLoaderError::InvalidKernelStartAddress);
        }

        let mem_offset = match kernel_start {
            Some(start) => start,
            None => GuestAddress(u64::from(boot_header.code32_start)),
        };

        boot_header.code32_start = mem_offset.raw_value() as u32;

        let mut loader_result: KernelLoaderResult = Default::default();
        loader_result.setup_header = Some(boot_header);
        loader_result.kernel_load = mem_offset;

        // Seek the compressed `vmlinux.bin` and read it to memory.
        kernel_image
            .seek(SeekFrom::Start(setup_size as u64))
            .map_err(|_| Error::SeekBzImageCompressedKernel)?;
        guest_mem
            .read_exact_from(mem_offset, kernel_image, kernel_size)
            .map_err(|_| Error::ReadBzImageCompressedKernel)?;

        loader_result.kernel_end = mem_offset
            .raw_value()
            .checked_add(kernel_size as GuestUsize)
            .ok_or(KernelLoaderError::MemoryOverflow)?;

        Ok(loader_result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::io::Cursor;
    use vm_memory::{Address, GuestAddress, GuestMemoryMmap};

    const MEM_SIZE: u64 = 0x100_0000;

    fn create_guest_mem() -> GuestMemoryMmap {
        GuestMemoryMmap::from_ranges(&[(GuestAddress(0x0), (MEM_SIZE as usize))]).unwrap()
    }

    fn make_bzimage() -> Vec<u8> {
        let mut v = Vec::new();
        v.extend_from_slice(include_bytes!("bzimage"));
        v
    }

    #[allow(safe_packed_borrows)]
    #[allow(non_snake_case)]
    #[test]
    fn test_load_bzImage() {
        let gm = create_guest_mem();
        let image = make_bzimage();
        let mut kernel_start = GuestAddress(0x200000);
        let mut highmem_start_address = GuestAddress(0x0);

        // load bzImage with good kernel_start and himem_start setting
        let mut loader_result = BzImage::load(
            &gm,
            Some(kernel_start),
            &mut Cursor::new(&image),
            Some(highmem_start_address),
        )
        .unwrap();

        assert_eq!(loader_result.kernel_load.raw_value(), 0x200000);
        assert_eq!(loader_result.setup_header.unwrap().header, 0x53726448);
        assert_eq!(loader_result.setup_header.unwrap().version, 0x20d);
        assert_eq!(loader_result.setup_header.unwrap().loadflags, 1);
        assert_eq!(loader_result.kernel_end, 0x60c320);

        // load bzImage without kernel_start
        loader_result = BzImage::load(
            &gm,
            None,
            &mut Cursor::new(&image),
            Some(highmem_start_address),
        )
        .unwrap();
        assert_eq!(loader_result.kernel_load.raw_value(), 0x100000);

        // load bzImage withouth himem_start
        loader_result = BzImage::load(&gm, None, &mut Cursor::new(&image), None).unwrap();
        assert_eq!(0x53726448, loader_result.setup_header.unwrap().header);
        assert_eq!(loader_result.kernel_load.raw_value(), 0x100000);

        // load bzImage with a bad himem setting
        kernel_start = GuestAddress(0x1000);
        highmem_start_address = GuestAddress(0x200000);

        assert_eq!(
            Some(KernelLoaderError::InvalidKernelStartAddress),
            BzImage::load(
                &gm,
                Some(kernel_start),
                &mut Cursor::new(&image),
                Some(highmem_start_address),
            )
            .err()
        );
    }
}
