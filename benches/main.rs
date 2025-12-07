// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

extern crate criterion;
extern crate linux_loader;
extern crate vm_memory;

use criterion::{criterion_group, criterion_main, Criterion};

#[cfg(all(
    any(target_arch = "x86", target_arch = "x86_64"),
    any(feature = "elf", feature = "pe", feature = "bzimage")
))]
mod x86_64;
#[cfg(all(
    any(target_arch = "x86", target_arch = "x86_64"),
    any(feature = "elf", feature = "pe", feature = "bzimage")
))]
use x86_64::*;

#[cfg(all(
    any(target_arch = "aarch64", target_arch = "riscv64"),
    any(feature = "elf", feature = "pe", feature = "bzimage")
))]
mod fdt;
#[cfg(all(
    any(target_arch = "aarch64", target_arch = "riscv64"),
    any(feature = "elf", feature = "pe", feature = "bzimage")
))]
pub use fdt::*;

// No-op benchmark when configurator module is not available
#[cfg(not(any(feature = "elf", feature = "pe", feature = "bzimage")))]
fn criterion_benchmark(_c: &mut Criterion) {}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(500);
    targets = criterion_benchmark
}

criterion_main! {
    benches
}
