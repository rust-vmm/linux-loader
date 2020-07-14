// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause
extern crate criterion;
extern crate linux_loader;
extern crate vm_memory;

use linux_loader::configurator::BootParams;
use vm_memory::{ByteValued, GuestAddress, GuestMemoryMmap};

const MEM_SIZE: usize = 0x100_0000;
const FDT_MAX_SIZE: usize = 0x20;

pub fn create_guest_memory() -> GuestMemoryMmap {
    GuestMemoryMmap::from_ranges(&[(GuestAddress(0x0), MEM_SIZE)]).unwrap()
}

#[derive(Clone, Copy, Default)]
pub struct FdtPlaceholder([u8; FDT_MAX_SIZE]);

unsafe impl ByteValued for FdtPlaceholder {}

pub fn build_fdt_boot_params() -> BootParams {
    let fdt = FdtPlaceholder([0u8; FDT_MAX_SIZE]);
    let fdt_addr = GuestAddress((MEM_SIZE - FDT_MAX_SIZE - 1) as u64);
    BootParams::new::<FdtPlaceholder>(&fdt, fdt_addr)
}
