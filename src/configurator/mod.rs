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

//! Traits and structs for configuring and loading boot parameters.
//! - [BootConfigurator](trait.BootConfigurator.html): configure boot parameters.
//! - [LinuxBootConfigurator](linux/struct.LinuxBootConfigurator.html): Linux boot protocol
//!   parameters configurator.
//! - [PvhBootConfigurator](pvh/struct.PvhBootConfigurator.html): PVH boot protocol parameters
//!   configurator.

use vm_memory::{ByteValued, GuestAddress, GuestMemory};

use std::error::Error as StdError;
use std::fmt;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod x86_64;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub use x86_64::*;

#[cfg(target_arch = "aarch64")]
mod aarch64;
#[cfg(target_arch = "aarch64")]
pub use aarch64::Error as ArmError;

/// Errors specific to boot protocol configuration.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// Errors specific to the Linux boot protocol configuration.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    Linux(linux::Error),
    /// Errors specific to the PVH boot protocol configuration.
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    Pvh(pvh::Error),
    /// Errors specific to device tree boot configuration.
    #[cfg(target_arch = "aarch64")]
    Arm(ArmError),
}

impl StdError for Error {
    fn description(&self) -> &str {
        use Error::*;
        match self {
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Linux(ref e) => e.description(),
            #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
            Pvh(ref e) => e.description(),
            #[cfg(target_arch = "aarch64")]
            Arm(ref e) => e.description(),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Boot Configurator Error: {}",
            StdError::description(self)
        )
    }
}

/// A specialized `Result` type for the boot configurator.
pub type Result<T> = std::result::Result<T, Error>;

/// Trait that defines interfaces for building (TBD) and configuring boot parameters.
///
/// Currently, this trait exposes a single function which writes user-provided boot parameters into
/// guest memory at the user-specified addresses. It's meant to be called after the kernel is
/// loaded and after the boot parameters are built externally (in the VMM).
///
/// This trait will be extended with additional functionality to build boot parameters.
pub trait BootConfigurator {
    /// Writes the boot parameters (configured elsewhere) into guest memory.
    ///
    /// The arguments are split into `header` and `sections` to accommodate different boot
    /// protocols like Linux boot and PVH. In Linux boot, the e820 map could be considered as
    /// `sections`, but it's already encapsulated in the `boot_params` and thus all the boot
    /// parameters are passed through a single struct. In PVH, the memory map table is separated
    /// from the `hvm_start_info` struct, therefore it's passed separately.
    ///
    /// # Arguments
    ///
    /// * `header` - header section of the boot parameters and address where to write it in guest
    ///              memory. The first element must be a POD struct that implements [`ByteValued`].
    ///              For the Linux protocol it's the [`boot_params`] struct, and for PVH the
    ///             [`hvm_start_info`] struct.
    /// * `sections` - vector of sections that compose the boot parameters and address where to
    ///                write them in guest memory. Unused for the Linux protocol. For PVH, it's the
    ///                memory map table represented as a vector of [`hvm_memmap_table_entry`]. Must
    ///                be a `Vec` of POD data structs that implement [`ByteValued`].
    /// * `guest_memory` - guest's physical memory.
    ///
    /// [`boot_params`]: ../loader/bootparam/struct.boot_e820_entry.html
    /// [`hvm_memmap_table_entry`]: ../loader/elf/start_info/struct.hvm_memmap_table_entry.html
    /// [`hvm_start_info`]: ../loader/elf/start_info/struct.hvm_start_info.html
    /// [`ByteValued`]: https://docs.rs/vm-memory/latest/vm_memory/bytes/trait.ByteValued.html
    fn write_bootparams<T, S, M>(
        header: (T, GuestAddress),
        sections: Option<(Vec<S>, GuestAddress)>,
        guest_memory: &M,
    ) -> Result<()>
    where
        T: ByteValued,
        S: ByteValued,
        M: GuestMemory;
}
