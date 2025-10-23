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

// Include architecture-specific benchmark modules.
// These modules are now expected to define a function (e.g., `benchmarks`)
// that will be called by the main `criterion_benchmark` function.
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod x86_64;

#[cfg(any(target_arch = "aarch64", target_arch = "riscv64"))]
mod fdt;

// Define the main benchmark function which dispatches to architecture-specific benchmarks.
// This centralizes the benchmark entry point and allows for more robust
// #[cfg] handling for 'all-features' compilation scenarios.
// If specific features cause conflicts for certain architectures,
// additional `#[cfg(feature = "...")]` guards can be added here
// around the calls to `x86_64::benchmarks` or `fdt::benchmarks`,
// or within the respective `x86_64` or `fdt` modules themselves.
fn criterion_benchmark(c: &mut Criterion) {
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    // The x86_64 module is expected to provide a `benchmarks` function.
    x86_64::benchmarks(c);

    #[cfg(any(target_arch = "aarch64", target_arch = "riscv64"))]
    // The fdt module is expected to provide a `benchmarks` function.
    fdt::benchmarks(c);

    // If no architecture-specific benchmarks are enabled (e.g., for an unsupported
    // target_arch or if specific feature combinations disable benchmarks),
    // this function will simply do nothing. This ensures that `criterion_benchmark`
    // always exists and compiles, preventing "undefined function" errors from the
    // `criterion_group!` macro during `all-features` and `all-targets` builds.
}

criterion_group! {
    name = benches;
    config = Criterion::default().sample_size(500);
    targets = criterion_benchmark
}

criterion_main! {
    benches
}