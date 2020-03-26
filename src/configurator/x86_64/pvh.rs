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

//! Traits and structs for configuring and loading boot parameters on `x86_64` using the PVH boot
//! protocol.

use vm_memory::{Address, ByteValued, Bytes, GuestAddress, GuestMemory};

use super::super::{BootConfigurator, Error as BootConfiguratorError, Result};
use crate::loader::elf::start_info::{hvm_memmap_table_entry, hvm_start_info};

use std::error::Error as StdError;
use std::fmt;
use std::mem;

/// Boot configurator for the PVH boot protocol.
pub struct PvhBootConfigurator {}

/// Errors specific to the PVH boot protocol configuration.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// No memory map wasn't passed to the boot configurator.
    MemmapTableMissing,
    /// The memory map table extends past the end of guest memory.
    MemmapTablePastRamEnd,
    /// Error writing memory map table to guest memory.
    MemmapTableSetup,
    /// The hvm_start_info structure extends past the end of guest memory.
    StartInfoPastRamEnd,
    /// Error writing hvm_start_info to guest memory.
    StartInfoSetup,
}

impl StdError for Error {
    fn description(&self) -> &str {
        use Error::*;
        match self {
            MemmapTableMissing => "No memory map wasn't passed to the boot configurator.",
            MemmapTablePastRamEnd => "The memory map table extends past the end of guest memory.",
            MemmapTableSetup => "Error writing memory map table to guest memory.",
            StartInfoPastRamEnd => {
                "The hvm_start_info structure extends past the end of guest memory."
            }
            StartInfoSetup => "Error writing hvm_start_info to guest memory.",
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "PVH Boot Configurator Error: {}",
            StdError::description(self)
        )
    }
}

impl From<Error> for BootConfiguratorError {
    fn from(err: Error) -> Self {
        BootConfiguratorError::Pvh(err)
    }
}

unsafe impl ByteValued for hvm_start_info {}
unsafe impl ByteValued for hvm_memmap_table_entry {}

impl BootConfigurator for PvhBootConfigurator {
    /// Writes the boot parameters (configured elsewhere) into guest memory.
    ///
    /// # Arguments
    ///
    /// * `header` - boot parameters encapsulated in a [`hvm_start_info`] struct.
    /// * `sections` - memory map table represented as a vector of [`hvm_memmap_table_entry`].
    /// * `guest_memory` - guest's physical memory.
    ///
    /// [`hvm_start_info`]: ../loader/elf/start_info/struct.hvm_start_info
    /// [`hvm_memmap_table_entry`]: ../loader/elf/start_info/struct.hvm_memmap_table_entry.html
    fn write_bootparams<T, S, M>(
        header: (T, GuestAddress),
        sections: Option<(Vec<S>, GuestAddress)>,
        guest_memory: &M,
    ) -> Result<()>
    where
        T: ByteValued,
        S: ByteValued,
        M: GuestMemory,
    {
        // The VMM has filled an `hvm_start_info` struct and a `Vec<hvm_memmap_table_entry>`
        // and has passed them on to this function.
        // The `hvm_start_info` will be written at `addr` and the memmap entries at
        // `start_info.0.memmap_paddr`.
        let (memmap_entries, mut memmap_start_addr) = sections.ok_or(Error::MemmapTableMissing)?;
        guest_memory
            .checked_offset(
                memmap_start_addr,
                mem::size_of::<hvm_memmap_table_entry>() * memmap_entries.len(),
            )
            .ok_or(Error::MemmapTablePastRamEnd)?;

        for memmap_entry in memmap_entries {
            guest_memory
                .write_obj(memmap_entry, memmap_start_addr)
                .map_err(|_| Error::MemmapTableSetup)?;
            memmap_start_addr =
                memmap_start_addr.unchecked_add(mem::size_of::<hvm_memmap_table_entry>() as u64);
        }

        guest_memory
            .checked_offset(header.1, mem::size_of::<hvm_start_info>())
            .ok_or(Error::StartInfoPastRamEnd)?;
        guest_memory
            .write_obj(header.0, header.1)
            .map_err(|_| Error::StartInfoSetup)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use vm_memory::{Address, GuestAddress, GuestMemoryMmap};

    const XEN_HVM_START_MAGIC_VALUE: u32 = 0x336ec578;
    const MEM_SIZE: u64 = 0x1000000;
    const E820_RAM: u32 = 1;

    fn create_guest_mem() -> GuestMemoryMmap {
        GuestMemoryMmap::from_ranges(&[(GuestAddress(0x0), (MEM_SIZE as usize))]).unwrap()
    }

    fn add_memmap_entry(
        memmap_entries: &mut Vec<hvm_memmap_table_entry>,
        addr: GuestAddress,
        size: u64,
        mem_type: u32,
    ) {
        // Add the table entry to the vector
        memmap_entries.push(hvm_memmap_table_entry {
            addr: addr.raw_value(),
            size,
            type_: mem_type,
            reserved: 0,
        });
    }

    fn build_bootparams_common() -> (hvm_start_info, Vec<hvm_memmap_table_entry>) {
        let mut start_info = hvm_start_info::default();
        let memmap_entries: Vec<hvm_memmap_table_entry> = vec![];

        start_info.magic = XEN_HVM_START_MAGIC_VALUE;
        start_info.version = 1;
        start_info.nr_modules = 0;
        start_info.memmap_entries = 0;

        (start_info, memmap_entries)
    }

    #[test]
    fn test_configure_pvh_boot() {
        let (mut start_info, mut memmap_entries) = build_bootparams_common();
        let guest_memory = create_guest_mem();

        let start_info_addr = GuestAddress(0x6000);
        let memmap_addr = GuestAddress(0x7000);
        start_info.memmap_paddr = memmap_addr.raw_value();

        // Error case: configure without memory map.
        assert_eq!(
            PvhBootConfigurator::write_bootparams::<
                hvm_start_info,
                hvm_memmap_table_entry,
                GuestMemoryMmap,
            >((start_info, start_info_addr), None, &guest_memory,)
            .err(),
            Some(Error::MemmapTableMissing.into())
        );

        // Error case: start_info doesn't fit in guest memory.
        let bad_start_info_addr = GuestAddress(
            guest_memory.last_addr().raw_value() - mem::size_of::<hvm_start_info>() as u64 + 1,
        );
        assert_eq!(
            PvhBootConfigurator::write_bootparams::<
                hvm_start_info,
                hvm_memmap_table_entry,
                GuestMemoryMmap,
            >(
                (start_info, bad_start_info_addr),
                Some((memmap_entries.clone(), memmap_addr)),
                &guest_memory,
            )
            .err(),
            Some(Error::StartInfoPastRamEnd.into())
        );

        // Error case: memory map doesn't fit in guest memory.
        let himem_start = GuestAddress(0x100000);
        add_memmap_entry(&mut memmap_entries, himem_start, 0, E820_RAM);
        let bad_memmap_addr = GuestAddress(
            guest_memory.last_addr().raw_value() - mem::size_of::<hvm_memmap_table_entry>() as u64
                + 1,
        );
        assert_eq!(
            PvhBootConfigurator::write_bootparams::<
                hvm_start_info,
                hvm_memmap_table_entry,
                GuestMemoryMmap,
            >(
                (start_info, start_info_addr),
                Some((memmap_entries.clone(), bad_memmap_addr)),
                &guest_memory,
            )
            .err(),
            Some(Error::MemmapTablePastRamEnd.into())
        );

        assert!(PvhBootConfigurator::write_bootparams::<
            hvm_start_info,
            hvm_memmap_table_entry,
            GuestMemoryMmap,
        >(
            (start_info, start_info_addr),
            Some((memmap_entries.clone(), memmap_addr)),
            &guest_memory,
        )
        .is_ok());
    }
}
