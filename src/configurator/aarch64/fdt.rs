// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

//! Traits and structs for loading the device tree.

use vm_memory::{ByteValued, Bytes, GuestAddress, GuestMemory};

use std::error::Error as StdError;
use std::fmt;

use super::super::{BootConfigurator, Error as BootConfiguratorError, Result};

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
    /// * `fdt` - flattened device tree.
    /// * `sections` - unused.
    /// * `guest_memory` - guest's physical memory.
    fn write_bootparams<T, S, M>(
        fdt: (T, GuestAddress),
        _sections: Option<(Vec<S>, GuestAddress)>,
        guest_memory: &M,
    ) -> Result<()>
    where
        T: ByteValued,
        S: ByteValued,
        M: GuestMemory,
    {
        // The VMM has filled an FDT and passed it as a `ByteValued` object.
        guest_memory
            .write_obj(fdt.0, fdt.1)
            .map_err(|_| Error::WriteFDTToMemory.into())
    }
}
