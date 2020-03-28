// Copyright (c) 2019 Intel Corporation. All rights reserved.
// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

//! Traits and structs for loading pe image kernels into guest memory.

#![cfg(feature = "pe")]

use std::error::{self, Error as StdError};
use std::fmt::{self, Display};
use std::io::{Read, Seek, SeekFrom};
use std::mem;

use vm_memory::{Address, ByteValued, Bytes, GuestAddress, GuestMemory, GuestUsize};

use super::super::{Error as KernelLoaderError, KernelLoader, KernelLoaderResult, Result};

/// ARM64 Image (PE) format support
pub struct PE;

unsafe impl ByteValued for arm64_image_header {}

#[derive(Debug, PartialEq)]
/// PE kernel loader errors.
pub enum Error {
    /// Unable to seek to Image end.
    SeekImageEnd,
    /// Unable to seek to Image header.
    SeekImageHeader,
    /// Unable to read kernel image.
    ReadKernelImage,
    /// Unable to read Image header.
    ReadImageHeader,
    /// Invalid Image binary.
    InvalidImage,
    /// Invalid Image magic number.
    InvalidImageMagicNumber,
}

impl error::Error for Error {
    fn description(&self) -> &str {
        match self {
            Error::SeekImageEnd => "Unable to seek Image end",
            Error::SeekImageHeader => "Unable to seek Image header",
            Error::ReadImageHeader => "Unable to read Image header",
            Error::InvalidImage => "Invalid Image",
            Error::InvalidImageMagicNumber => "Invalid Image magic number",
            Error::ReadKernelImage => "Unable to read kernel image",
        }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "PE Kernel Loader Error: {}", self.description())
    }
}

#[repr(C)]
#[derive(Debug, Copy, Clone, Default)]
// See kernel doc Documentation/arm64/booting.txt for more information.
// All these fields should be little endian.
struct arm64_image_header {
    code0: u32,
    code1: u32,
    text_offset: u64,
    image_size: u64,
    flags: u64,
    res2: u64,
    res3: u64,
    res4: u64,
    magic: u32,
    res5: u32,
}

impl KernelLoader for PE {
    /// Loads a PE Image into guest memory.
    ///
    /// # Arguments
    ///
    /// * `guest_mem` - The guest memory where the kernel image is loaded.
    /// * `kernel_start` - The offset into 'guest_mem' at which to load the kernel.
    /// * `kernel_image` - Input Image format kernel image.
    /// * `highmem_start_address` - ignored on ARM64.
    ///
    /// # Returns
    /// * KernelLoaderResult
    fn load<F, M: GuestMemory>(
        guest_mem: &M,
        kernel_start: Option<GuestAddress>,
        kernel_image: &mut F,
        _highmem_start_address: Option<GuestAddress>,
    ) -> Result<KernelLoaderResult>
    where
        F: Read + Seek,
    {
        let kernel_size = kernel_image
            .seek(SeekFrom::End(0))
            .map_err(|_| Error::SeekImageEnd)? as usize;
        let mut arm64_header: arm64_image_header = Default::default();
        kernel_image
            .seek(SeekFrom::Start(0))
            .map_err(|_| Error::SeekImageHeader)?;

        arm64_header
            .as_bytes()
            .read_from(0, kernel_image, mem::size_of::<arm64_image_header>())
            .map_err(|_| Error::ReadImageHeader)?;

        if u32::from_le(arm64_header.magic) != 0x644d_5241 {
            return Err(Error::InvalidImageMagicNumber.into());
        }

        let image_size = u64::from_le(arm64_header.image_size);
        let mut text_offset = u64::from_le(arm64_header.text_offset);

        if image_size == 0 {
            text_offset = 0x80000;
        }

        let mem_offset = kernel_start
            .unwrap_or(GuestAddress(0))
            .checked_add(text_offset)
            .ok_or(Error::InvalidImage)?;

        let mut loader_result: KernelLoaderResult = Default::default();
        loader_result.kernel_load = mem_offset;

        kernel_image
            .seek(SeekFrom::Start(0))
            .map_err(|_| Error::SeekImageHeader)?;
        guest_mem
            .read_exact_from(mem_offset, kernel_image, kernel_size)
            .map_err(|_| Error::ReadKernelImage)?;

        loader_result.kernel_end = mem_offset
            .raw_value()
            .checked_add(kernel_size as GuestUsize)
            .ok_or(KernelLoaderError::MemoryOverflow)?;

        Ok(loader_result)
    }
}
