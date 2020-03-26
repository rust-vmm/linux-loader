// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

//! Traits and structs for configuring and loading boot parameters on `aarch64`.

#![cfg(target_arch = "aarch64")]

use std::error::Error as StdError;
use std::fmt;

/// Placeholder error type.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// Placeholder error value.
    Placeholder,
}

impl StdError for Error {
    fn description(&self) -> &str {
        unimplemented!()
    }
}

impl fmt::Display for Error {
    fn fmt(&self, _f: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
}
