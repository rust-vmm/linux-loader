// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

#![cfg(any(target_arch = "x86", target_arch = "x86_64"))]

extern crate linux_loader;
extern crate vm_memory;

use linux_loader::configurator::BootParams;
use linux_loader::loader::elf::start_info::{hvm_memmap_table_entry, hvm_start_info};
use vm_memory::{Address, GuestAddress, GuestMemoryMmap};

const MEM_SIZE: usize = 0x100_0000;
const E820_RAM: u32 = 1;
const XEN_HVM_START_MAGIC_VALUE: u32 = 0x336ec578;

pub fn create_guest_memory() -> GuestMemoryMmap {
    GuestMemoryMmap::from_ranges(&[(GuestAddress(0x0), MEM_SIZE)]).unwrap()
}

pub fn create_elf_pvh_image() -> Vec<u8> {
    include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/src/loader/x86_64/elf/test_elfnote.bin"
    ))
    .to_vec()
}

pub fn build_boot_params() -> (hvm_start_info, Vec<hvm_memmap_table_entry>) {
    let mut start_info = hvm_start_info::default();
    let memmap_entry = hvm_memmap_table_entry {
        addr: 0x7000,
        size: 0,
        type_: E820_RAM,
        reserved: 0,
    };
    start_info.magic = XEN_HVM_START_MAGIC_VALUE;
    start_info.version = 1;
    start_info.nr_modules = 0;
    start_info.memmap_entries = 0;
    (start_info, vec![memmap_entry])
}

pub fn build_pvh_boot_params() -> BootParams {
    let (mut start_info, memmap_entries) = build_boot_params();
    // Address in guest memory where the `start_info` struct will be written.
    let start_info_addr = GuestAddress(0x6000);
    // Address in guest memory where the memory map will be written.
    let memmap_addr = GuestAddress(0x7000);
    start_info.memmap_paddr = memmap_addr.raw_value();
    // Write boot parameters in guest memory.
    let mut boot_params = BootParams::new::<hvm_start_info>(&start_info, start_info_addr);
    boot_params.set_sections::<hvm_memmap_table_entry>(&memmap_entries, memmap_addr);
    boot_params
}
