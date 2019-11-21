// Copyright (c) 2019 Intel Corporation. All rights reserved.
// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

#![deny(missing_docs)]

//! A Linux kernel image loading crate.
//!
//! This crate offers support for loading raw ELF/PE (vmlinux) and compressed
//! big zImage (bzImage) kernel images.
//! Support for any other kernel image format can be added by implementing
//! the KernelLoader.
//!
//! # Platform support
//!
//! - x86_64
//! - aarch64
//!
//! This crates supports kernel image in format:
//! - vmlinux and bzImage on x86_64 platform.
//! - PE on aarch64 platform.
//!
//! Extending it to support other kernel image formats will make it consumable
//! by other platforms.

pub mod cmdline;
pub mod loader;

extern crate vm_memory;
