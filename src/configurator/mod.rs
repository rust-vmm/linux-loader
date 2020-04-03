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
pub use aarch64::*;

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
    Fdt(fdt::Error),
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
            Fdt(ref e) => e.description(),
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
    /// * `params` - struct containing the header section of the boot parameters, additional
    ///              sections and modules, and their associated addresses in guest memory. These
    ///              vary with the boot protocol used.
    /// * `guest_memory` - guest's physical memory.
    fn write_bootparams<M>(params: BootParams, guest_memory: &M) -> Result<()>
    where
        M: GuestMemory;
}

/// Boot parameters to be written in guest memory.
#[derive(Clone)]
pub struct BootParams {
    /// "Header section", always written in guest memory irrespective of boot protocol.
    pub header: (Vec<u8>, GuestAddress),
    /// Optional sections containing boot configurations (e.g. E820 map).
    pub sections: Option<(Vec<u8>, GuestAddress)>,
    /// Optional modules specified at boot configuration time.
    pub modules: Option<(Vec<u8>, GuestAddress)>,
}

impl BootParams {
    /// Creates a new [`BootParams`](struct.BootParams.html) struct with the specified header.
    ///
    /// # Arguments
    ///
    /// * `header` - [`ByteValued`] representation of mandatory boot parameters.
    /// * `header_addr` - address in guest memory where `header` will be written.
    ///
    /// [`ByteValued`]: https://docs.rs/vm-memory/latest/vm_memory/bytes/trait.ByteValued.html
    pub fn new<T: ByteValued>(header: &T, header_addr: GuestAddress) -> Self {
        BootParams {
            header: (header.as_slice().to_vec(), header_addr),
            sections: None,
            modules: None,
        }
    }

    /// Adds or overwrites the boot sections and associated memory address.
    ///
    /// Unused on `aarch64` and for the Linux boot protocol.
    /// For the PVH boot protocol, the sections specify the memory map table in
    /// [`hvm_memmap_table_entry`] structs.
    ///
    /// # Arguments
    ///
    /// * `sections` - vector of [`ByteValued`] boot configurations.
    /// * `sections_addr` - address where the sections will be written in guest memory.
    ///
    /// [`ByteValued`]: https://docs.rs/vm-memory/latest/vm_memory/bytes/trait.ByteValued.html
    /// [`hvm_memmap_table_entry`]: ../loader/elf/start_info/struct.hvm_memmap_table_entry.html
    pub fn add_sections<T: ByteValued>(&mut self, sections: &[T], sections_addr: GuestAddress) {
        self.sections = Some((
            sections
                .iter()
                .flat_map(|section| section.as_slice().to_vec())
                .collect(),
            sections_addr,
        ));
    }

    /// Adds or overwrites the boot modules and associated memory address.
    ///
    /// Unused on `aarch64` and for the Linux boot protocol.
    /// For the PVH boot protocol, the modules are specified in [`hvm_modlist_entry`] structs.
    ///
    /// # Arguments
    ///
    /// * `modules` - vector of [`ByteValued`] boot configurations.
    /// * `modules_addr` - address where the modules will be written in guest memory.
    ///
    /// [`ByteValued`]: https://docs.rs/vm-memory/latest/vm_memory/bytes/trait.ByteValued.html
    /// [`hvm_modlist_entry`]: ../loader/elf/start_info/struct.hvm_modlist_entry.html
    pub fn add_modules<T: ByteValued>(&mut self, modules: &[T], modules_addr: GuestAddress) {
        self.modules = Some((
            modules
                .iter()
                .flat_map(|module| module.as_slice().to_vec())
                .collect(),
            modules_addr,
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_messages() {
        #[cfg(target_arch = "x86_64")]
        {
            // Linux
            assert_eq!(
                format!("{}", Error::Linux(linux::Error::ZeroPagePastRamEnd)),
                "Boot Configurator Error: The zero page extends past the end of guest memory."
            );
            assert_eq!(
                format!("{}", Error::Linux(linux::Error::ZeroPageSetup)),
                "Boot Configurator Error: Error writing to the zero page of guest memory."
            );

            // PVH
            assert_eq!(
                format!("{}", Error::Pvh(pvh::Error::MemmapTableMissing)),
                "Boot Configurator Error: No memory map was passed to the boot configurator."
            );
            assert_eq!(
                format!("{}", Error::Pvh(pvh::Error::MemmapTablePastRamEnd)),
                "Boot Configurator Error: \
                 The memory map table extends past the end of guest memory."
            );
            assert_eq!(
                format!("{}", Error::Pvh(pvh::Error::MemmapTableSetup)),
                "Boot Configurator Error: Error writing memory map table to guest memory."
            );
            assert_eq!(
                format!("{}", Error::Pvh(pvh::Error::StartInfoPastRamEnd)),
                "Boot Configurator Error: \
                 The hvm_start_info structure extends past the end of guest memory."
            );
            assert_eq!(
                format!("{}", Error::Pvh(pvh::Error::StartInfoSetup)),
                "Boot Configurator Error: Error writing hvm_start_info to guest memory."
            );
        }

        #[cfg(target_arch = "aarch64")]
        // FDT
        assert_eq!(
            format!("{}", Error::Fdt(fdt::Error::WriteFDTToMemory)),
            "Boot Configurator Error: Error writing FDT in guest memory."
        );
    }
}
