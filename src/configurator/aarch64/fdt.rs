// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

//! Traits and structs for loading the device tree.

use vm_memory::{Bytes, GuestMemory};

use std::error::Error as StdError;
use std::fmt;

use crate::configurator::{BootConfigurator, BootParams, Error as BootConfiguratorError, Result};

/// Errors specific to the device tree boot protocol configuration.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// Error writing FDT in memory.
    WriteFDTToMemory,
}

impl StdError for Error {
    fn description(&self) -> &str {
        use Error::*;
        match self {
            WriteFDTToMemory => "Error writing FDT in guest memory.",
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Device Tree Boot Configurator Error: {}",
            StdError::description(self)
        )
    }
}

impl From<Error> for BootConfiguratorError {
    fn from(err: Error) -> Self {
        BootConfiguratorError::Fdt(err)
    }
}

/// Boot configurator for device tree.
pub struct FdtBootConfigurator {}

impl BootConfigurator for FdtBootConfigurator {
    /// Writes the boot parameters (configured elsewhere) into guest memory.
    ///
    /// # Arguments
    ///
    /// * `params` - boot parameters containing the FDT.
    /// * `guest_memory` - guest's physical memory.
    fn write_bootparams<M>(params: BootParams, guest_memory: &M) -> Result<()>
    where
        M: GuestMemory,
    {
        // The VMM has filled an FDT and passed it as a `ByteValued` object.
        guest_memory
            .write_slice(params.header.as_slice(), params.header_start)
            .map_err(|_| Error::WriteFDTToMemory.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use vm_memory::{Address, ByteValued, GuestAddress, GuestMemoryMmap};

    const FDT_MAX_SIZE: usize = 0x20;
    const MEM_SIZE: u64 = 0x100_0000;

    fn create_guest_mem() -> GuestMemoryMmap {
        GuestMemoryMmap::from_ranges(&[(GuestAddress(0x0), (MEM_SIZE as usize))]).unwrap()
    }

    #[derive(Clone, Copy, Default)]
    struct FdtPlaceholder([u8; FDT_MAX_SIZE]);
    unsafe impl ByteValued for FdtPlaceholder {}

    #[test]
    fn test_configure_fdt_boot() {
        let fdt = FdtPlaceholder([0u8; FDT_MAX_SIZE]);
        let guest_memory = create_guest_mem();

        // Error case: FDT doesn't fit in guest memory.
        let fdt_addr = guest_memory
            .last_addr()
            .checked_sub(FDT_MAX_SIZE as u64 - 2)
            .unwrap();
        assert_eq!(
            FdtBootConfigurator::write_bootparams::<GuestMemoryMmap>(
                BootParams::new::<FdtPlaceholder>(&fdt, fdt_addr),
                &guest_memory,
            )
            .err(),
            Some(Error::WriteFDTToMemory.into())
        );

        let fdt_addr = guest_memory
            .last_addr()
            .checked_sub(FDT_MAX_SIZE as u64 - 1)
            .unwrap();
        assert!(FdtBootConfigurator::write_bootparams::<GuestMemoryMmap>(
            BootParams::new::<FdtPlaceholder>(&fdt, fdt_addr),
            &guest_memory,
        )
        .is_ok());
    }

    #[test]
    fn test_error_messages() {
        assert_eq!(
            format!("{}", Error::WriteFDTToMemory),
            "Device Tree Boot Configurator Error: Error writing FDT in guest memory."
        )
    }
}
