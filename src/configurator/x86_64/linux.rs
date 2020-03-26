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

//! Traits and structs for configuring and loading boot parameters on `x86_64` using the Linux
//! boot protocol.

use vm_memory::{ByteValued, Bytes, GuestAddress, GuestMemory};

use super::super::{BootConfigurator, Error as BootConfiguratorError, Result};
use crate::loader::bootparam::boot_params;

use std::error::Error as StdError;
use std::fmt;
use std::mem;

/// Boot configurator for the Linux boot protocol.
pub struct LinuxBootConfigurator {}

/// Errors specific to the Linux boot protocol configuration.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// The zero page extends past the end of guest memory.
    ZeroPagePastRamEnd,
    /// Error writing to the zero page of guest memory.
    ZeroPageSetup,
}

impl StdError for Error {
    fn description(&self) -> &str {
        use Error::*;
        match self {
            ZeroPagePastRamEnd => "The zero page extends past the end of guest memory.",
            ZeroPageSetup => "Error writing to the zero page of guest memory.",
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Linux Boot Configurator Error: {}",
            StdError::description(self)
        )
    }
}

impl From<Error> for BootConfiguratorError {
    fn from(err: Error) -> Self {
        BootConfiguratorError::Linux(err)
    }
}

impl BootConfigurator for LinuxBootConfigurator {
    /// Writes the boot parameters (configured elsewhere) into guest memory.
    ///
    /// # Arguments
    ///
    /// * `header` - boot parameters encapsulated in a [`boot_params`] struct.
    /// * `sections` - unused.
    /// * `guest_memory` - guest's physical memory.
    ///
    /// [`boot_params`]: ../loader/bootparam/struct.boot_e820_entry.html
    fn write_bootparams<T, S, M>(
        header: (T, GuestAddress),
        _sections: Option<(Vec<S>, GuestAddress)>,
        guest_memory: &M,
    ) -> Result<()>
    where
        T: ByteValued,
        S: ByteValued,
        M: GuestMemory,
    {
        // The VMM has filled a `boot_params` struct and its e820 map.
        // This will be written in guest memory at the zero page.
        guest_memory
            .checked_offset(header.1, mem::size_of::<boot_params>())
            .ok_or(Error::ZeroPagePastRamEnd)?;
        guest_memory
            .write_obj(header.0, header.1)
            .map_err(|_| Error::ZeroPageSetup)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem;
    use vm_memory::{Address, GuestAddress, GuestMemoryMmap};

    const KERNEL_BOOT_FLAG_MAGIC: u16 = 0xaa55;
    const KERNEL_HDR_MAGIC: u32 = 0x53726448;
    const KERNEL_LOADER_OTHER: u8 = 0xff;
    const KERNEL_MIN_ALIGNMENT_BYTES: u32 = 0x1000000;
    const MEM_SIZE: u64 = 0x1000000;

    fn create_guest_mem() -> GuestMemoryMmap {
        GuestMemoryMmap::from_ranges(&[(GuestAddress(0x0), (MEM_SIZE as usize))]).unwrap()
    }

    fn build_bootparams_common() -> boot_params {
        let mut params = boot_params::default();
        params.hdr.boot_flag = KERNEL_BOOT_FLAG_MAGIC;
        params.hdr.header = KERNEL_HDR_MAGIC;
        params.hdr.kernel_alignment = KERNEL_MIN_ALIGNMENT_BYTES;
        params.hdr.type_of_loader = KERNEL_LOADER_OTHER;
        params
    }

    #[test]
    fn test_configure_linux_boot() {
        let zero_page_addr = GuestAddress(0x30000);

        let params = build_bootparams_common();
        // This is where we'd append e820 entries, cmdline, PCI, ACPI etc.

        let guest_memory = create_guest_mem();

        // Error case: boot params don't fit in guest memory (zero page address too close to end).
        let bad_zeropg_addr = GuestAddress(
            guest_memory.last_addr().raw_value() - mem::size_of::<boot_params>() as u64 + 1,
        );
        assert_eq!(
            LinuxBootConfigurator::write_bootparams::<boot_params, boot_params, GuestMemoryMmap>(
                (params, bad_zeropg_addr),
                None,
                &guest_memory,
            )
            .err(),
            Some(Error::ZeroPagePastRamEnd.into()),
        );

        // Success case.
        assert!(
            LinuxBootConfigurator::write_bootparams::<boot_params, boot_params, GuestMemoryMmap>(
                (params, zero_page_addr),
                None,
                &guest_memory
            )
            .is_ok()
        );
    }
}
