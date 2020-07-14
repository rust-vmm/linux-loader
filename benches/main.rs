// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause
extern crate criterion;
extern crate linux_loader;
extern crate vm_memory;

use criterion::{black_box, criterion_group, criterion_main, Criterion};

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod x86_64;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use x86_64::*;

#[cfg(target_arch = "aarch64")]
mod aarch64;
#[cfg(target_arch = "aarch64")]
use aarch64::*;

#[cfg(target_arch = "aarch64")]
use linux_loader::configurator::fdt::FdtBootConfigurator;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use linux_loader::configurator::pvh::PvhBootConfigurator;
use linux_loader::configurator::BootConfigurator;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use linux_loader::loader::elf::Elf;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use linux_loader::loader::KernelLoader;
use vm_memory::GuestMemoryMmap;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use std::io::Cursor;

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub fn criterion_benchmark(c: &mut Criterion) {
    let guest_mem = create_guest_memory();

    let elf_pvh_image = create_elf_pvh_image();
    let pvh_boot_params = build_pvh_boot_params();

    c.bench_function("load_elf_pvh", |b| {
        b.iter(|| {
            black_box(Elf::load(
                &guest_mem,
                None,
                &mut Cursor::new(&elf_pvh_image),
                None,
            ))
            .unwrap();
        })
    });

    c.bench_function("configure_pvh", |b| {
        b.iter(|| {
            black_box(PvhBootConfigurator::write_bootparams::<GuestMemoryMmap>(
                pvh_boot_params.clone(),
                &guest_mem,
            ))
            .unwrap();
        })
    });
}

#[cfg(target_arch = "aarch64")]
pub fn criterion_benchmark(c: &mut Criterion) {
    let guest_mem = create_guest_memory();
    let fdt_boot_params = build_fdt_boot_params();
    c.bench_function("configure_fdt", |b| {
        b.iter(|| {
            black_box(FdtBootConfigurator::write_bootparams::<GuestMemoryMmap>(
                fdt_boot_params.clone(),
                &guest_mem,
            ))
            .unwrap();
        })
    });
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(500);
    targets = criterion_benchmark
}

criterion_main! {
    benches
}
